Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Sumbool.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.

Section RaftRefinementInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Record electionsData := mkElectionsData {
                              votes : list (term * name) ;
                              votesWithLog : list (term * name * list entry) ;
                              cronies : term -> list name ;
                              leaderLogs : list (term * list entry) ;
                              allEntries : list (term * entry)
                            }.

  Definition update_elections_data_requestVote (me : name) (src : name) t candidateId lastLogIndex lastLogTerm st :=
    let (st', r) :=
        handleRequestVote me (snd st) t candidateId lastLogIndex lastLogTerm
    in
    match (votedFor (snd st), votedFor st') with
      | (None, Some cid) =>
        {| votes := (currentTerm st', cid) :: votes (fst st) ;
           votesWithLog := (currentTerm st', cid, log st') :: votesWithLog (fst st) ;
           cronies := cronies (fst st) ;
           leaderLogs := leaderLogs (fst st) ;
           allEntries := allEntries (fst st)
        |}
      | (Some cid, Some cid') =>
        if andb (beq_nat (currentTerm (snd st)) (currentTerm st')) (if name_eq_dec cid cid' then true else false) then
          fst st
        else
          {| votes := (currentTerm st', cid') :: votes (fst st) ;
             votesWithLog := (currentTerm st', cid', log st') :: votesWithLog (fst st) ;
             cronies := cronies (fst st) ;
             leaderLogs := leaderLogs (fst st) ;
             allEntries := allEntries (fst st)
          |}
      | _ => fst st
    end.

  Definition update_elections_data_requestVoteReply (me : name) (src : name) t voteGranted st :=
    let st' := handleRequestVoteReply me (snd st) src t voteGranted in
    match (type st') with
      | Follower => fst st
      | Candidate =>
        {| votes := votes (fst st) ;
           votesWithLog := votesWithLog (fst st) ;
           cronies :=
             fun tm => (if eq_nat_dec tm (currentTerm st') then
                         votesReceived st'
                       else
                         cronies (fst st) tm) ;
           leaderLogs := leaderLogs (fst st) ;
           allEntries := allEntries (fst st)
        |}
      | Leader =>
        {| votes := votes (fst st) ;
           votesWithLog := votesWithLog (fst st) ;
           cronies :=
             fun tm => (if eq_nat_dec tm (currentTerm st') then
                         votesReceived st'
                       else
                         cronies (fst st) tm) ;
           leaderLogs := if serverType_eq_dec (type (snd st)) Candidate then
                           (currentTerm st', log st') :: leaderLogs (fst st)
                         else
                           leaderLogs (fst st) ;
           allEntries := allEntries (fst st)
        |}
    end.

  Definition update_elections_data_appendEntries
             (me : name)
             st (t : term) (leaderId : name) (prevLogIndex : logIndex)
             (prevLogTerm : term) (entries : list entry) (leaderCommit : logIndex) :=
    let (_, m) := handleAppendEntries me (snd st) t leaderId prevLogIndex
                                      prevLogTerm entries leaderCommit in
    match m with
      | AppendEntriesReply t entries true =>
        {| votes := votes (fst st) ;
           votesWithLog := votesWithLog (fst st) ;
           cronies := cronies (fst st) ;
           leaderLogs := leaderLogs (fst st) ;
           allEntries := (map (fun e => (t, e)) entries) ++ allEntries (fst st)
        |}
      | _ => fst st
    end.


  Definition update_elections_data_net (me : name) (src: name) (m : msg) st : electionsData :=
    match m with
      | RequestVote t candidateId lastLogIndex lastLogTerm =>
        update_elections_data_requestVote me src t src lastLogIndex lastLogTerm st
      | RequestVoteReply t voteGranted =>
        update_elections_data_requestVoteReply me src t voteGranted st
      | AppendEntries t lid prevLogIndex prevLogTerm entries leaderCommit =>
        update_elections_data_appendEntries me st t lid prevLogIndex prevLogTerm entries leaderCommit
      | _ => fst st
    end.

  Definition update_elections_data_timeout (me : name) st : electionsData :=
    let '(_, st', _) := handleTimeout me (snd st) in
    match (votedFor st') with
      | Some cid =>
        if serverType_eq_dec (type (snd st)) Leader then
          fst st
        else
          {| votes := (currentTerm st', cid) :: votes (fst st) ;
             votesWithLog := (currentTerm st', cid, log st') :: votesWithLog (fst st) ;
             cronies :=
               if serverType_eq_dec (type st') Candidate then
                 fun tm => (if eq_nat_dec tm (currentTerm st') then
                             votesReceived st'
                           else
                             cronies (fst st) tm)
               else
                 cronies (fst st) ;
             leaderLogs := leaderLogs (fst st) ;
             allEntries := allEntries (fst st)
          |}
      | None => fst st
    end.


  Definition update_elections_data_client_request (me : name) st client id c : electionsData :=
    let '(_, st', _) := handleClientRequest me (snd st) client id c in
    if length (log (snd st)) <? length (log st') then
      match (log st') with
        | e :: _ => 
          {| votes := votes (fst st) ;
             votesWithLog := votesWithLog (fst st) ;
             cronies := cronies (fst st) ;
             leaderLogs := leaderLogs (fst st) ;
             allEntries := (currentTerm st', e) :: allEntries (fst st)
        |}
        | [] => fst st
      end
    else fst st.

  Definition update_elections_data_input (me : name) (inp : raft_input) st : electionsData :=
    match inp with
      | Timeout => update_elections_data_timeout me st
      | ClientRequest client id c => update_elections_data_client_request me st client id c
    end.

  Instance elections_ghost_params : GhostFailureParams failure_params :=
    {
      ghost_data := electionsData ;
      ghost_init := {| votes := [] ; votesWithLog := []; cronies := fun _ => [];
                 leaderLogs := [] ;
                 allEntries := [] |} ;
      ghost_net_handlers := update_elections_data_net ;
      ghost_input_handlers := update_elections_data_input
    }.

  Definition raft_refined_base_params := refined_base_params.
  Definition raft_refined_multi_params := refined_multi_params.
  Definition raft_refined_failure_params := refined_failure_params.

  Hint Extern 4 (@BaseParams) => apply raft_refined_base_params : typeclass_instances.
  Hint Extern 4 (@MultiParams _) => apply raft_refined_multi_params : typeclass_instances.
  Hint Extern 4 (@FailureParams _ _) => apply raft_refined_failure_params : typeclass_instances.

  Inductive refined_raft_intermediate_reachable : network -> Prop :=
  | RRIR_init : refined_raft_intermediate_reachable step_m_init
  | RRIR_step_f :
      forall failed net failed' net' out,
        refined_raft_intermediate_reachable net ->
        step_f (failed, net) (failed', net') out ->
        refined_raft_intermediate_reachable net'
  | RRIR_handleInput :
      forall net h inp gd out d l ps' st',
        refined_raft_intermediate_reachable net ->
        handleInput h inp (snd (nwState net h)) = (out, d, l) ->
        update_elections_data_input h inp (nwState net h) = gd ->
        (forall h', st' h' = update (nwState net) h (gd, d) h') ->
        (forall p', In p' ps' -> In p' (nwPackets net) \/
                           In p' (send_packets h l)) ->
        refined_raft_intermediate_reachable (mkNetwork ps' st')
  | RRIR_handleMessage :
      forall p net xs ys st' ps' gd d l,
        refined_raft_intermediate_reachable net ->
        handleMessage (pSrc p) (pDst p) (pBody p) (snd (nwState net (pDst p))) = (d, l) ->
        update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = gd ->
        nwPackets net = xs ++ p :: ys ->
        (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
        (forall p', In p' ps' -> In p' (xs ++ ys) \/
                           In p' (send_packets (pDst p) l)) ->
        refined_raft_intermediate_reachable (mkNetwork ps' st')
  | RRIR_doLeader :
      forall net st' ps' h os gd d d' ms,
        refined_raft_intermediate_reachable net ->
        doLeader d h = (os, d', ms) ->
        nwState net h = (gd, d) ->
        (forall h', st' h' = update (nwState net) h (gd, d') h') ->
        (forall p, In p ps' -> In p (nwPackets net) \/
                         In p (send_packets h ms)) ->
        refined_raft_intermediate_reachable (mkNetwork ps' st')
  | RRIR_doGenericServer :
      forall net st' ps' os gd d d' ms h,
        refined_raft_intermediate_reachable net ->
        doGenericServer h d = (os, d', ms) ->
        nwState net h = (gd, d) ->
        (forall h', st' h' = update (nwState net) h (gd, d') h') ->
        (forall p, In p ps' -> In p (nwPackets net) \/
                         In p (send_packets h ms)) ->
        refined_raft_intermediate_reachable (mkNetwork ps' st').

  Definition refined_raft_net_invariant_client_request (P : network -> Prop) :=
    forall h net st' ps' gd out d l client id c,
      handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) ->
      gd = update_elections_data_client_request h (nwState net h) client id c ->
      P net ->
      refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_timeout (P : network -> Prop) :=
    forall net h st' ps' gd out d l,
      handleTimeout h (snd (nwState net h)) = (out, d, l) ->
      gd = update_elections_data_timeout h (nwState net h) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                               In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_append_entries (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t n pli plt es ci,
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) ->
      gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci ->
      pBody p = AppendEntries t n pli plt es ci ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_append_entries_reply (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t es res,
      handleAppendEntriesReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t es res = (d, m) ->
      gd = (fst (nwState net (pDst p))) ->
      pBody p = AppendEntriesReply t es res ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         In p' (send_packets (pDst p) m)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_request_vote (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t cid lli llt,
      handleRequestVote (pDst p) (snd (nwState net (pDst p))) t (pSrc p) lli llt  = (d, m) ->
      gd = update_elections_data_requestVote (pDst p) (pSrc p) t (pSrc p) lli llt (nwState net (pDst p)) ->
      pBody p = RequestVote t cid lli llt ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_request_vote_reply (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d t v,
      handleRequestVoteReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t v = d ->
      gd = update_elections_data_requestVoteReply (pDst p) (pSrc p) t v (nwState net (pDst p)) ->
      pBody p = RequestVoteReply t v ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_do_leader (P : network -> Prop) :=
    forall net st' ps' gd d h os d' ms,
      doLeader d h = (os, d', ms) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_do_generic_server (P : network -> Prop) :=
    forall net st' ps' gd d os d' ms h,
      doGenericServer h d = (os, d', ms) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_state_same_packet_subset (P : network -> Prop) :=
    forall net net',
      (forall h, nwState net h = nwState net' h) ->
      (forall p, In p (nwPackets net') -> In p (nwPackets net)) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      P net'.

  Definition refined_raft_net_invariant_reboot (P : network -> Prop) :=
    forall net net' gd d h d',
      reboot d = d' ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwState net h = (gd, d) ->
      (forall h', nwState net' h' = update (nwState net) h (gd, d') h') ->
      nwPackets net = nwPackets net' ->
      P net'.

  Definition refined_raft_net_invariant_init (P : network -> Prop) :=
    P step_m_init.

  Definition refined_raft_net_invariant_client_request' (P : network -> Prop) :=
    forall h net st' ps' gd out d l client id c,
      handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) ->
      gd = update_elections_data_client_request h (nwState net h) client id c ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_timeout' (P : network -> Prop) :=
    forall net h st' ps' gd out d l,
      handleTimeout h (snd (nwState net h)) = (out, d, l) ->
      gd = update_elections_data_timeout h (nwState net h) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                               In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_append_entries' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t n pli plt es ci,
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) ->
      gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci ->
      pBody p = AppendEntries t n pli plt es ci ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_append_entries_reply' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t es res,
      handleAppendEntriesReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t es res = (d, m) ->
      gd = (fst (nwState net (pDst p))) ->
      pBody p = AppendEntriesReply t es res ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         In p' (send_packets (pDst p) m)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_request_vote' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t cid lli llt,
      handleRequestVote (pDst p) (snd (nwState net (pDst p))) t (pSrc p) lli llt  = (d, m) ->
      gd = update_elections_data_requestVote (pDst p) (pSrc p) t (pSrc p) lli llt (nwState net (pDst p)) ->
      pBody p = RequestVote t cid lli llt ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_request_vote_reply' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d t v,
      handleRequestVoteReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t v = d ->
      gd = update_elections_data_requestVoteReply (pDst p) (pSrc p) t v (nwState net (pDst p)) ->
      pBody p = RequestVoteReply t v ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_do_leader' (P : network -> Prop) :=
    forall net st' ps' gd d h os d' ms,
      doLeader d h = (os, d', ms) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_do_generic_server' (P : network -> Prop) :=
    forall net st' ps' gd d os d' ms h,
      doGenericServer h d = (os, d', ms) ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Definition refined_raft_net_invariant_reboot' (P : network -> Prop) :=
    forall net net' gd d h d',
      reboot d = d' ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable net' ->
      nwState net h = (gd, d) ->
      (forall h', nwState net' h' = update (nwState net) h (gd, d') h') ->
      nwPackets net = nwPackets net' ->
      P net'.


  Class raft_refinement_interface : Prop :=
    {
      refined_raft_net_invariant :
        forall P net,
          refined_raft_net_invariant_init P ->
          refined_raft_net_invariant_client_request P ->
          refined_raft_net_invariant_timeout P ->
          refined_raft_net_invariant_append_entries P ->
          refined_raft_net_invariant_append_entries_reply P ->
          refined_raft_net_invariant_request_vote P ->
          refined_raft_net_invariant_request_vote_reply P ->
          refined_raft_net_invariant_do_leader P ->
          refined_raft_net_invariant_do_generic_server P ->
          refined_raft_net_invariant_state_same_packet_subset P ->
          refined_raft_net_invariant_reboot P ->
          refined_raft_intermediate_reachable net ->
          P net;
      refined_raft_net_invariant' :
        forall P net,
          refined_raft_net_invariant_init P ->
          refined_raft_net_invariant_client_request' P ->
          refined_raft_net_invariant_timeout' P ->
          refined_raft_net_invariant_append_entries' P ->
          refined_raft_net_invariant_append_entries_reply' P ->
          refined_raft_net_invariant_request_vote' P ->
          refined_raft_net_invariant_request_vote_reply' P ->
          refined_raft_net_invariant_do_leader' P ->
          refined_raft_net_invariant_do_generic_server' P ->
          refined_raft_net_invariant_state_same_packet_subset P ->
          refined_raft_net_invariant_reboot' P ->
          refined_raft_intermediate_reachable net ->
          P net;
      lift_prop :
        forall (P : _ -> Prop),
          (forall net, raft_intermediate_reachable net -> P net) ->
          (forall net, refined_raft_intermediate_reachable net -> P (deghost net));
      lower_prop :
        forall P : _ -> Prop,
          (forall net, refined_raft_intermediate_reachable net -> P (deghost net)) ->
          (forall net, raft_intermediate_reachable net -> P net);
      deghost_spec :
        forall (net : @network _ raft_refined_multi_params) h,
          nwState (deghost net) h = snd (nwState net h);
      simulation_1 :
        forall net,
          refined_raft_intermediate_reachable net ->
          raft_intermediate_reachable (deghost net)
    }.

End RaftRefinementInterface.

Hint Extern 4 (@BaseParams) => apply raft_refined_base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply raft_refined_multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply raft_refined_failure_params : typeclass_instances.
