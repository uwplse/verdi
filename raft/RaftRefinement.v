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


Section GhostElections.
  
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Record electionsData := mkElectionsData {
                              votes : list (term * name) ;
                              votesWithLog : list (term * name * list entry) ;
                              cronies : term -> list name ;
                              leaderLogs : list (term * list entry) ;
                              appendEntriesReplies : list (term * entry)
                            }.

  Definition update_elections_data_requestVote (me : name) (src : name) t candidateId lastLogIndex lastLogTerm st :=
    let (st', r) := 
        handleRequestVote me (snd st) t candidateId lastLogIndex lastLogTerm
    in
    match (votedFor st') with
      | Some cid =>
        {| votes := (currentTerm st', cid) :: votes (fst st) ;
           votesWithLog := (currentTerm st', cid, log st') :: votesWithLog (fst st) ;
           cronies := cronies (fst st) ;
           leaderLogs := leaderLogs (fst st) ;
           appendEntriesReplies := appendEntriesReplies (fst st)
        |}
      | None => fst st
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
           appendEntriesReplies := appendEntriesReplies (fst st)
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
           appendEntriesReplies := appendEntriesReplies (fst st)
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
           appendEntriesReplies := (map (fun e => (t, e)) entries) ++ appendEntriesReplies (fst st)
        |}
      | _ => fst st
    end.
  
  
  Definition update_elections_data_net (me : name) (src: name) (m : msg) st : electionsData :=
    match m with
      | RequestVote t candidateId lastLogIndex lastLogTerm =>
        update_elections_data_requestVote me src t src lastLogIndex lastLogTerm st
      | RequestVoteReply t voteGranted =>
        update_elections_data_requestVoteReply me src t voteGranted st
      | AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit =>
        update_elections_data_appendEntries me st t leaderId prevLogIndex prevLogTerm entries leaderCommit
      | _ => fst st
    end.

  Definition update_elections_data_timeout (me : name) st : electionsData :=
    let '(_, st', _) := handleTimeout me (snd st) in
    match (votedFor st') with
      | Some cid =>
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
           appendEntriesReplies := appendEntriesReplies (fst st)
        |}
      | None => fst st
    end.

  Definition update_elections_data_input (me : name) (inp : raft_input) st : electionsData :=
    match inp with
      | Timeout => update_elections_data_timeout me st
      | _ => fst st
    end.

  Instance elections_ghost_params : GhostFailureParams failure_params :=
    {
      ghost_data := electionsData ;
      ghost_init := {| votes := [] ; votesWithLog := []; cronies := fun _ => [];
                 leaderLogs := [] ;
                 appendEntriesReplies := [] |} ;
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
      gd = fst (nwState net h) ->
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

  Lemma refined_raft_invariant_handle_message P :
    forall xs p ys net st' ps' gd d l,
      refined_raft_net_invariant_append_entries P ->
      refined_raft_net_invariant_append_entries_reply P ->
      refined_raft_net_invariant_request_vote P ->
      refined_raft_net_invariant_request_vote_reply P ->
      handleMessage (pSrc p) (pDst p) (pBody p) (snd (nwState net (pDst p))) = (d, l) ->
      update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = gd ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage, update_elections_data_net in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop refined_raft_net_invariant_request_vote|
     eapply_prop refined_raft_net_invariant_request_vote_reply|
     eapply_prop refined_raft_net_invariant_append_entries|
     eapply_prop refined_raft_net_invariant_append_entries_reply]; eauto;
    unfold send_packets in *; simpl in *; intros; subst; auto; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma refined_raft_invariant_handle_input P :
    forall h inp net st' ps' gd out d l,
      refined_raft_net_invariant_timeout P ->
      refined_raft_net_invariant_client_request P ->
      handleInput h inp (snd (nwState net h)) = (out, d, l) ->
      update_elections_data_input h inp (nwState net h) = gd ->
      P net ->
      refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput, update_elections_data_input in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop refined_raft_net_invariant_timeout|
     eapply_prop refined_raft_net_invariant_client_request]; eauto; subst; auto.
  Qed.

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
  
  Theorem refined_raft_net_invariant :
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
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       + unfold refined_net_handlers in *. simpl in *.
         unfold RaftNetHandler, update_elections_data_net in *.
         repeat break_let.
         repeat find_inversion.
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2;
                nwState := update (nwState net) (pDst p)
                                  (update_elections_data_net (pDst p) 
                                                             (pSrc p)
                                                             (pBody p)
                                                             (nwState net (pDst p)), r0) |})
           by (eapply RRIR_handleMessage; eauto; in_crush).
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := ((xs ++ ys)
                                ++ send_packets (pDst p) l2)
                               ++ send_packets (pDst p) l3 ;
            nwState := update
                         (nwState
                            {|
                              nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2;
                              nwState := update (nwState net) 
                                                (pDst p)
                                                (update_elections_data_net 
                                                   (pDst p) (pSrc p) 
                                                   (pBody p) (nwState net (pDst p)), r0) |})
                         (pDst p)
                         (update_elections_data_net (pDst p) 
                                                    (pSrc p) (pBody p) (nwState net (pDst p)), r1) |})
           by
             (eapply RRIR_doGenericServer; eauto;
              [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop refined_raft_net_invariant_do_leader. eauto. 
         eapply_prop refined_raft_net_invariant_do_generic_server. eauto.
         eapply refined_raft_invariant_handle_message with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or. auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. in_crush.
       + unfold refined_input_handlers in *. simpl in *.
         unfold RaftInputHandler, update_elections_data_input in *. repeat break_let.
         repeat find_inversion.
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := nwPackets net ++ send_packets h l2;
                nwState := update (nwState net) h
                                  (update_elections_data_input h
                                                               inp
                                                               (nwState net h), r0) |})
           by (eapply RRIR_handleInput; eauto; in_crush).
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net
                                ++ send_packets h l2)
                               ++ send_packets h l4 ;
            nwState := update
                         (nwState
                            {|
                              nwPackets := nwPackets net ++ send_packets h l2;
                              nwState := update (nwState net) 
                                                h
                                                (update_elections_data_input h inp
                                                                             (nwState net h), r0) |})
                         h
                         (update_elections_data_input h inp (nwState net h), r1) |})
           by
             (eapply RRIR_doGenericServer; eauto;
              [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop refined_raft_net_invariant_do_leader. eauto.
         eapply_prop refined_raft_net_invariant_do_generic_server. eauto.
         eapply refined_raft_invariant_handle_input with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or.
         auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. unfold send_packets.  intros. in_crush.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end. 
         eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end. 
         eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop refined_raft_net_invariant_reboot; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
         destruct (nwState net h); auto.
    - eapply refined_raft_invariant_handle_input; eauto.
    - eapply refined_raft_invariant_handle_message; eauto.
    - eapply_prop refined_raft_net_invariant_do_leader; eauto.
    - eapply_prop refined_raft_net_invariant_do_generic_server; eauto.
  Qed.

  Require Import FunctionalExtensionality.

  Ltac workhorse :=
    try match goal with
        | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal
      end;
    try match goal with
        | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros
      end;
      repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => invc H
             end;
      repeat (simpl in *; subst);
      repeat rewrite map_app;
      repeat rewrite map_map.


  Theorem simulation_1 :
    forall net,
      refined_raft_intermediate_reachable net ->
      raft_intermediate_reachable (deghost net).
  Proof.
    intros.
    induction H.
    - constructor.
    - simpl in *.
      pose proof (RIR_step_f).
      specialize (H1 failed (deghost net) failed' (deghost net') out).
      apply H1; auto.
      apply ghost_simulation_1; auto.
    - unfold deghost in *. simpl in *.
      eapply RIR_handleInput; eauto.
      + simpl in *. repeat break_match. simpl in *.
        assert (nwState h = (g, d0)) by eauto.
        repeat find_rewrite. eauto.
      + intros. simpl in *.
        repeat break_match; subst; simpl in *;
        repeat find_higher_order_rewrite; break_if; subst; simpl in *;
        congruence.
      + intros. simpl in *. in_crush.
        find_apply_hyp_hyp.
        in_crush.
    - unfold deghost in *. simpl in *.
      pose proof (RIR_handleMessage).
      specialize
        (H5 (@mkPacket _ multi_params
                       (pSrc p)
                       (pDst p)
                       (pBody p))).
      eapply H5; eauto.
      + simpl in *. repeat break_match. simpl in *.
        repeat find_rewrite. eauto.
      + simpl in *.
        unfold raft_refined_base_params, raft_refined_multi_params in *.
        simpl in *.
        repeat find_rewrite.
        map_crush. eauto.
      + intros. repeat break_match. simpl in *.
        repeat find_higher_order_rewrite.
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
    - unfold deghost in *. simpl in *.
      eapply RIR_doLeader; eauto.
      + simpl in *. repeat break_match. simpl in *.
        assert (nwState h = (g, d0)) by eauto.
        repeat find_rewrite. repeat find_inversion. eauto.
      + simpl in *.
        intros. repeat break_match; simpl in *;
        repeat find_higher_order_rewrite;
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
    - unfold deghost in *. simpl in *.
      eapply RIR_doGenericServer; eauto.
      + simpl in *. repeat break_match. simpl in *.
        assert (nwState h = (g, d0)) by eauto.
        repeat find_rewrite. repeat find_inversion. eauto.
      + simpl in *.
        intros. repeat break_match; simpl in *;
        repeat find_higher_order_rewrite;
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
  Qed.

  Theorem lift_prop :
    forall P,
      (forall net, raft_intermediate_reachable net -> P net) ->
      (forall net, refined_raft_intermediate_reachable net -> P (deghost net)).
  Proof.
    intros.
    eauto using simulation_1.
  Qed.

  Require Import FunctionalExtensionality.
  
  Theorem simulation_2 :
    forall net,
      raft_intermediate_reachable net ->
      exists rnet,
        net = deghost rnet /\
        refined_raft_intermediate_reachable rnet.
  Proof.
    intros.
    induction H.
    - exists (reghost step_m_init). intuition.
        unfold reghost. constructor.
    - break_exists. break_and.
      apply ghost_simulation_2 with (gnet := x) in H0; auto.
      repeat (break_exists; intuition).
      subst.
      exists x0. intuition.
      eapply RRIR_step_f; eauto.
    - break_exists. break_and. 
      subst. 
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) h (update_elections_data_input h inp (nwState x h), d)
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *.
        eapply RRIR_handleInput; repeat break_match; simpl in *; eauto.
        simpl in *. in_crush.
        find_apply_hyp_hyp. in_crush.
        destruct x. auto.
    - break_exists. break_and. 
      subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) (pDst p)
                             (update_elections_data_net (pDst p) (pSrc p)
                                                 (pBody p) (nwState x (pDst p)), d)
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *.
        eapply RRIR_handleMessage with (p := ghost_packet p);
          repeat break_match; simpl in *; eauto.
        * simpl in *.
          match goal with
        | H : map _ ?la = ?lb |- _ =>
          symmetry in H;
            pose proof @map_inverses _ _ la lb deghost_packet ghost_packet
          end.
          repeat (forwards; [intro a; destruct a; reflexivity|]; concludes;
                  match goal with
                    | H :  forall _ : packet,  _ = _ |- _ => clear H
                  end).
          concludes. map_crush. eauto.
        * simpl in *. in_crush.
          find_apply_hyp_hyp. in_crush.
    - break_exists. break_and. subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) h (fst (nwState x h) , d')
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *. simpl in *. repeat break_match; simpl in *.
        eapply RRIR_doLeader with (d := d) (h := h);
          repeat (break_match; simpl in *); eauto.
        * simpl in *. find_rewrite. simpl in *. auto.
        * simpl in *. in_crush.
          find_apply_hyp_hyp. in_crush.
          destruct x. auto.
    - break_exists. break_and. subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) h (fst (nwState x h) , d')
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *. simpl in *. repeat break_match; simpl in *.
        eapply RRIR_doGenericServer with (d := d) (h := h);
          repeat (break_match; simpl in *); eauto.
        * simpl in *. find_rewrite. simpl in *. auto.
        * simpl in *. in_crush.
          find_apply_hyp_hyp. in_crush.
          destruct x. auto.
  Qed.
  
  Theorem lower_prop :
    forall P : _ -> Prop,
      (forall net, refined_raft_intermediate_reachable net -> P (deghost net)) ->
      (forall net, raft_intermediate_reachable net -> P net).
  Proof.
    intros.
    find_apply_lem_hyp simulation_2.
    break_exists. intuition. subst. eauto.
  Qed.
  
  Lemma deghost_spec :
    forall (net : @network _ raft_refined_multi_params) h,
      nwState (deghost net) h = snd (nwState net h).
  Proof.
    intros.
    destruct net; auto.
  Qed.
End GhostElections.


Hint Extern 4 (@BaseParams) => apply raft_refined_base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply raft_refined_multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply raft_refined_failure_params : typeclass_instances.
