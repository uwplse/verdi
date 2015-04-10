Require Import Arith.
Require Import NPeano.
Require Import PeanoNat.
Import Nat.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import VerdiTactics.
Require Import RaftState.

Open Scope bool.

Set Implicit Arguments.

Class RaftParams (orig_base_params : BaseParams)
  := {
      N : nat ;
      input_eq_dec : forall x y : input, {x = y} + {x <> y} ;
      output_eq_dec : forall x y : output, {x = y} + {x <> y}
    }.

Section Raft.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition term := nat.
  Definition logIndex := nat.
  Definition name := fin N.
  Definition nodes : list name := all_fin _.
  Definition name_eq_dec : forall x y : name, {x = y} + {x <> y} := fin_eq_dec _.

  
  Notation "a >? b" := (b <? a) (at level 42).
  Notation "a >=? b" := (b <=? a) (at level 42).
  Notation "a == b" := (beq_nat a b) (at level 42).
  Notation "a != b" := (negb (beq_nat a b)) (at level 42).

  Notation "a === b" := (if fin_eq_dec _ a b then true else false) (at level 42).
  
  Record entry := mkEntry {
                      eAt : name;
                      eClient : nat;
                      eId : nat;
                      eIndex : logIndex;
                      eTerm : term;
                      eInput : input
                    }.

  Inductive msg : Type :=
  | RequestVote : term -> name -> logIndex -> term -> msg
  | RequestVoteReply : term -> bool -> msg
  | AppendEntries : term -> (name) -> logIndex -> term -> (list entry) -> logIndex -> msg
  | AppendEntriesReply : term -> (list entry) -> bool -> msg.

  Inductive raft_input : Type :=
  | Timeout : raft_input
  | ClientRequest : nat -> nat -> input -> raft_input.

  Inductive raft_output : Type :=
  | NotLeader : nat -> nat -> raft_output
  | ClientResponse : nat -> nat -> output -> raft_output.
  
  Inductive serverType : Set :=
  | Follower
  | Candidate
  | Leader.

  Definition serverType_eq_dec : forall x y : serverType, {x = y} + {x <> y}.
  Proof.
    repeat decide equality.
  Defined.
  
  Definition msg_eq_dec : forall x y: msg, {x = y} + {x <> y}.
  Proof.
    repeat decide equality; eauto using name_eq_dec, input_eq_dec.
  Qed.
  
  Definition entry_eq_dec : forall x y : entry, {x = y} + {x <> y}.
  Proof.
    repeat decide equality; eauto using input_eq_dec, name_eq_dec.
  Qed.

  Definition raft_data :=
    RaftState.raft_data term name entry logIndex serverType data output.

  Notation currentTerm         := (RaftState.currentTerm term name entry logIndex serverType data output).
  Notation votedFor            := (RaftState.votedFor term name entry logIndex serverType data output).
  Notation leaderId            := (RaftState.leaderId term name entry logIndex serverType data output).
  Notation log                 := (RaftState.log term name entry logIndex serverType data output).
  Notation commitIndex         := (RaftState.commitIndex term name entry logIndex serverType data output).
  Notation lastApplied         := (RaftState.lastApplied term name entry logIndex serverType data output).
  Notation nextIndex           := (RaftState.nextIndex term name entry logIndex serverType data output).
  Notation matchIndex          := (RaftState.matchIndex term name entry logIndex serverType data output).
  Notation shouldSend          := (RaftState.shouldSend term name entry logIndex serverType data output).
  Notation votesReceived       := (RaftState.votesReceived term name entry logIndex serverType data output).
  Notation type                := (RaftState.type term name entry logIndex serverType data output).
  Notation clientCache := (RaftState.clientCache term name entry logIndex serverType data output).
  Notation stateMachine := (RaftState.stateMachine term name entry logIndex serverType data output).
  Notation electoralVictories := (RaftState.electoralVictories term name entry logIndex serverType data output).
  Notation mkRaft_data              := (RaftState.mkRaft_data term name entry logIndex serverType data output).

  Fixpoint findAtIndex (entries : list entry) (i : logIndex) : option entry :=
    match entries with
      | nil => None
      | e :: es => if eIndex e == i then
                    Some e
                  else
                    if eIndex e <? i then
                      None
                    else
                      findAtIndex es i
    end.

  Fixpoint findGtIndex (entries : list entry) (i : logIndex) : list entry :=
    match entries with
      | nil => nil
      | e :: es => if (eIndex e) >? i then
                    e :: findGtIndex es i
                  else
                    nil
    end.

  Fixpoint removeAfterIndex (entries : list entry) (i : logIndex) : list entry :=
    match entries with
      | nil => nil
      | e :: es => if leb (eIndex e) i then
                    e :: es
                  else
                    removeAfterIndex es i
    end.

  Fixpoint maxIndex (entries : list entry) : logIndex :=
    match entries with
      | nil => 0
      | e :: es => eIndex e
    end.

  Fixpoint maxTerm (entries : list entry) : term :=
    match entries with
      | nil => 0
      | e :: es => eTerm e
    end.

  Definition advanceCurrentTerm state newTerm :=
    if newTerm >? (currentTerm state) then
      {[ {[ {[ {[ state with currentTerm := newTerm ]}
               with votedFor := None ]}
            with type := Follower ]}
           with leaderId := None ]}
    else
      state.

  Definition getNextIndex state h :=
    assoc_default name_eq_dec (nextIndex state) h (maxIndex (log state)).

  Definition tryToBecomeLeader (me : name) (state : raft_data)
    : list raft_output * raft_data * list (name * msg) :=
    let t := S (currentTerm state) in
    ([], {[ {[ {[ {[ state with type := Candidate ]}
              with votedFor := (Some me) ]}
           with votesReceived := [me] ]}
        with currentTerm := t ]},
     map (fun node => (node, RequestVote t
                                        me
                                        (maxIndex (log state))
                                        (maxTerm (log state))))
         (filter (fun h => if name_eq_dec me h then
                            false
                          else
                            true)
                 nodes)
    ).

  Definition not_empty {A} (l : list A) :=
    match l with
      | [] => false
      | _ => true
    end.

  Definition haveNewEntries (state : raft_data) (entries : list entry) :=
    andb (not_empty entries) (match findAtIndex (log state) (maxIndex entries) with
                                | None => true
                                | Some e => (negb (beq_nat (maxTerm entries) (eTerm e)))
                              end).

  Definition handleAppendEntries (me : name)
             (state : raft_data) (t : term) (leaderId : name) (prevLogIndex : logIndex)
             (prevLogTerm : term) (entries : list entry) (leaderCommit : logIndex) : raft_data * msg :=
    if currentTerm state >? t then
      (state, AppendEntriesReply (currentTerm state) entries false)
    else
      if prevLogIndex == 0 then
        if (haveNewEntries state entries) then
          ({[ {[ {[ {[ (advanceCurrentTerm state t)
                    with log := entries ]}
                    with commitIndex :=
                      max (commitIndex state) (min leaderCommit (maxIndex entries))
               ]}
              with type := Follower ]} with leaderId := Some leaderId ]},
           AppendEntriesReply t entries true)
        else
          ({[ {[ (advanceCurrentTerm state t)
                 with type := Follower ]} with leaderId := Some leaderId ]},
           AppendEntriesReply t entries true)
      else
        match (findAtIndex (log state) prevLogIndex) with
          | None => (state, AppendEntriesReply (currentTerm state) entries false)
          | Some e => if negb (beq_nat prevLogTerm (eTerm e)) then
                       (state, AppendEntriesReply (currentTerm state) entries false)
                     else
                       if haveNewEntries state entries then
                         let log' := removeAfterIndex (log state) prevLogIndex in
                         let log'' := entries ++ log' in
                         ({[ {[ {[ {[ (advanceCurrentTerm state t)
                                   with log := log'' ]}
                                with commitIndex :=
                                     max (commitIndex state) (min leaderCommit (maxIndex log''))
                              ]}
                             with type := Follower ]} with leaderId := Some leaderId ]},
                          AppendEntriesReply t entries true)
                       else
                         ({[ {[ (advanceCurrentTerm state t)
                                with type := Follower ]} with leaderId := Some leaderId ]},
                          AppendEntriesReply t entries true)
        end.

  Definition handleAppendEntriesReply (me : name) state src term entries (result : bool)
  : raft_data * list (name * msg) :=
    if result then
      let index := maxIndex entries in
      ({[ {[ state with matchIndex :=
               (assoc_set name_eq_dec (matchIndex state) src (max (assoc_default name_eq_dec (matchIndex state) src 0) index))
           ]}
          with nextIndex :=
            (assoc_set name_eq_dec (nextIndex state) src (max (getNextIndex state src) (S index)))
        ]},
       [])
    else
      if currentTerm state != term then
        (* shit, we're behind. need to convert to follower *)
        ({[ (advanceCurrentTerm state term) with type := Follower ]}, [])
      else
        ({[ state with nextIndex :=
              (assoc_set name_eq_dec (nextIndex state) src
                         (pred (getNextIndex state src)))
          ]},
         []).


  Definition moreUpToDate t1 i1 t2 i2 := (t1 >? t2) || ((t1 == t2) && (i1 >=? i2)).

  Definition handleRequestVote (me : name) state t candidateId lastLogIndex lastLogTerm : raft_data * msg :=
    if currentTerm state >? t then
      (state, RequestVoteReply (currentTerm state) false)
    else
      let state := (advanceCurrentTerm state t) in
      if andb (if leaderId state then false else true)
              (moreUpToDate lastLogTerm lastLogIndex (maxTerm (log state)) (maxIndex (log state)))
      then
        match (votedFor state) with
          | None => ({[ state with votedFor := Some candidateId ]},
                    RequestVoteReply (currentTerm state) true)
          | Some candidateId' =>
            (state, RequestVoteReply (currentTerm state) (candidateId === candidateId'))
        end
      else
        (state, RequestVoteReply (currentTerm state) false).

  Fixpoint div2 a :=
    match a with
      | S (S n) => S (div2 n)
      | 1 => 0
      | 0 => 0
    end.

  Definition wonElection (votes : list name) : bool :=
    (S (div2 (length nodes)) <=? length votes).

  Definition handleRequestVoteReply (me : name) state src t (voteGranted : bool) : raft_data :=
    if t >? (currentTerm state) then
      {[ (advanceCurrentTerm state t) with type := Follower ]}
    else if t <? (currentTerm state) then state else
           let won := voteGranted
                        && wonElection (dedup name_eq_dec (src :: votesReceived state)) in
           match (type state) with
             | Candidate => 
               {[ {[ {[ {[ {[ state
                              with votesReceived := (if voteGranted then
                                                       [src]
                                                     else
                                                       []) ++ votesReceived state ]}
                           with type := if won then
                                          Leader         (* long live the king *)
                                        else
                                          type state ]}
                        with matchIndex := [] ]}
                       with nextIndex := [] ]}
                  with electoralVictories :=
                    (if won then
                       [(currentTerm state, src :: votesReceived state, log state)]
                     else
                       []) ++ electoralVictories state ]}
             | _ => state
      end.

  Definition handleMessage (src : name) (me : name) (m : msg)
             (state : raft_data) : raft_data * list (name * msg) :=
    match m with
      | AppendEntries t lid prevLogIndex prevLogTerm entries leaderCommit =>
        let (st, r) :=
            handleAppendEntries me state t lid prevLogIndex prevLogTerm entries leaderCommit
        in
        (st, [(src, r)])
      | AppendEntriesReply term entries result => handleAppendEntriesReply me state src term entries result
      | RequestVote t candidateId lastLogIndex lastLogTerm =>
        let (st, r) := 
            handleRequestVote me state t src lastLogIndex lastLogTerm
        in
        (st, [(src, r)])
      | RequestVoteReply t voteGranted =>
        (handleRequestVoteReply me state src t voteGranted, [])
    end.

  Definition getLastId state client :=
    assoc eq_nat_dec (clientCache state) client.

  Definition applyEntry st e :=
    let (out, d) := handler (eInput e) (stateMachine st) in
    ([out], {[ {[ st with clientCache := assoc_set eq_nat_dec (clientCache st) (eClient e) (eId e, out) ]}
             with stateMachine := d ]}).

  Definition cacheApplyEntry st e :=
    match getLastId st (eClient e) with
      | Some (id, o) =>
        if eId e <? id then
          ([], st)
        else
          if eId e =? id then
            ([o], st)
          else
            applyEntry st e
      | None => applyEntry st e
    end.

  Fixpoint applyEntries h (st : raft_data) entries : (list raft_output * raft_data) :=
    match entries with
      | [] => ([], st)
      | e :: es =>
        let (out, st) := cacheApplyEntry st e in
        let out := if name_eq_dec (eAt e) h then
                     map (fun o => ClientResponse (eClient e) (eId e) o) out
                   else
                     [] in
        let (out', state) := applyEntries h st es in
        (out ++ out', state)
    end.

  Definition doGenericServer (h : name) (state : raft_data) :
    (list raft_output * raft_data * list (name * msg)) :=
    let (out, state) :=
        applyEntries h state
                     (rev (filter (fun x => andb (ltb (lastApplied state) (eIndex x))
                                                (leb (eIndex x) (commitIndex state)))
                                  (findGtIndex (log state) (lastApplied state)))) in
    (out, {[ state with lastApplied := if commitIndex state >? lastApplied state then
                                         (commitIndex state)
                                       else
                                         (lastApplied state)
              ]},
     []).

  Definition replicaMessage (state : raft_data) (me : name) (host : name) : (name * msg) :=
    let prevIndex := pred (getNextIndex state host) in
    let prevTerm := (match (findAtIndex (log state) prevIndex) with
                       | Some e => (eTerm e)
                       | None => 0
                     end) in
    let newEntries := findGtIndex (log state) prevIndex in
    (host, AppendEntries
             (currentTerm state) me prevIndex prevTerm newEntries (commitIndex state)).

  Definition haveQuorum (state : raft_data) (me : name) (N : logIndex) : bool :=
    ltb (div2 (length nodes)) (length (filter (fun h => leb N (assoc_default name_eq_dec (matchIndex state) h 0)) nodes)).
  
  Definition advanceCommitIndex (state : raft_data) (me : name) : raft_data :=
    let entriesToCommit :=
        filter (fun e =>
                  (currentTerm state == eTerm e) &&
                  (commitIndex state <? eIndex e) &&
                  (haveQuorum state me (eIndex e))) (findGtIndex (log state) (commitIndex state)) in
    {[ state with commitIndex := fold_left max (map eIndex entriesToCommit) (commitIndex state)]}.

  Definition doLeader (state : raft_data) (me : name) :
    (list raft_output * raft_data * list (name * msg)) :=
      match (type state) with
        | Leader => let state' := advanceCommitIndex state me in
                   if (shouldSend state') then
                     let state' := {[ state' with shouldSend := false ]} in
                     let replicaMessages := map (replicaMessage state' me)
                                                (filter (fun h => if name_eq_dec me h then
                                                                   false
                                                                 else
                                                                   true) nodes) in
                     ([], state', replicaMessages)
                   else
                     ([], state', [])
        | _ => ([], state, [])
      end.

  Definition RaftNetHandler (me : name) (src : name) (m : msg)
             (state : raft_data) :=
    let (state, pkts) := handleMessage src me m state in
    let '(genericOut, state, genericPkts) := doGenericServer me state in
    let '(leaderOut, state, leaderPkts) := doLeader state me in
    (genericOut ++ leaderOut,
     state, pkts ++ genericPkts ++ leaderPkts).

  Definition handleClientRequest (me : name) (state : raft_data) (client : nat) (id : nat) (c : input)
  : list raft_output * raft_data * list (name * msg) :=
    match (type state) with
      | Leader => let index := S (maxIndex (log state)) in
                 ([],
                  {[ {[ {[ state with log :=
                             (mkEntry me client id index (currentTerm state) c) :: (log state) ]}
                        with matchIndex :=
                          (assoc_set name_eq_dec (matchIndex state) me index)
                      ]}
                     with shouldSend := true ]},
                  [])
      | _ => ([NotLeader client id], state, [])
    end.

  
  Definition handleTimeout (me : name) (state : raft_data)
  : list raft_output * raft_data * list (name * msg) :=
    match (type state) with
      | Leader => ([], {[ state with shouldSend := true ]}, []) (* we automatically heartbeat elsewhere *)
      | _ => tryToBecomeLeader me state
    end.

  Definition handleInput (me : name) (inp : raft_input) (state : raft_data) :
    list raft_output * raft_data * list (name * msg) :=
    match inp with
      | ClientRequest client id c => handleClientRequest me state client id c
      | Timeout => handleTimeout me state
    end.

  Definition RaftInputHandler (me : name) (inp : raft_input)
             (state : raft_data) :=
    let '(handlerOut, state, pkts) := handleInput me inp state in
    let '(genericOut, state, genericPkts) := doGenericServer me state in
    let '(leaderOut, state, leaderPkts) := doLeader state me in
    (handlerOut ++ genericOut ++ leaderOut,
     state, pkts ++ genericPkts ++ leaderPkts).
  
  Definition reboot state : raft_data :=
    mkRaft_data (currentTerm state)
                (votedFor state)
                (leaderId state)
           (log state)
           0
           (lastApplied state)
           (stateMachine state)
           []
           []
           false
           []
           Follower
           (clientCache state)
           (electoralVictories state).

  Definition init_handlers (_ : name) : raft_data :=
    mkRaft_data 0
                None
                None
                []
                0
                0
                init
                []
                []
                false
                []
                Follower
                []
                [].

  Instance base_params : BaseParams :=
    {
      data := raft_data ;
      input := raft_input ;
      output := raft_output
    }.

  Instance multi_params : MultiParams _ :=
    {
      name := name ;
      msg := msg ;
      msg_eq_dec := msg_eq_dec ;
      name_eq_dec := name_eq_dec ;
      nodes := nodes ;
      init_handlers := init_handlers;
      net_handlers := RaftNetHandler ;
      input_handlers := RaftInputHandler
    }.
  Proof.
    - eauto using all_fin_all.
    - eauto using all_fin_NoDup.
  Defined.

  Instance failure_params : FailureParams _ :=
    {
      reboot := reboot
    }.

  Inductive raft_intermediate_reachable : network -> Prop :=
  | RIR_init : raft_intermediate_reachable step_m_init
  | RIR_step_f :
      forall failed net failed' net' out,
        raft_intermediate_reachable net ->
        step_f (failed, net) (failed', net') out ->
        raft_intermediate_reachable net'
  | RIR_handleInput :
      forall net h inp out d l ps' st',
        raft_intermediate_reachable net ->
        handleInput h inp (nwState net h) = (out, d, l) ->
        (forall h', st' h' = update (nwState net) h d h') ->
        (forall p', In p' ps' -> In p' (nwPackets net) \/
                           In p' (send_packets h l)) ->
        raft_intermediate_reachable (mkNetwork ps' st')
  | RIR_handleMessage :
      forall p net xs ys st' ps' d l,
        raft_intermediate_reachable net ->
        handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d, l) ->
        nwPackets net = xs ++ p :: ys ->
        (forall h, st' h = update (nwState net) (pDst p) d h) ->
        (forall p', In p' ps' -> In p' (xs ++ ys) \/
                           In p' (send_packets (pDst p) l)) ->
        raft_intermediate_reachable (mkNetwork ps' st')
  | RIR_doLeader :
      forall net st' ps' h os d' ms,
        raft_intermediate_reachable net ->
        doLeader (nwState net h) h = (os, d', ms) ->
        (forall h', st' h' = update (nwState net) h d' h') ->
        (forall p, In p ps' -> In p (nwPackets net) \/
                         In p (send_packets h ms)) ->
        raft_intermediate_reachable (mkNetwork ps' st')
  | RIR_doGenericServer :
      forall net st' ps' os d' ms h,
        raft_intermediate_reachable net ->
        doGenericServer h (nwState net h) = (os, d', ms) ->
        (forall h', st' h' = update (nwState net) h d' h') ->
        (forall p, In p ps' -> In p (nwPackets net) \/
                         In p (send_packets h ms)) ->
        raft_intermediate_reachable (mkNetwork ps' st').

  Lemma step_f_star_raft_intermediate_reachable' :
    forall n' tr,
      step_f_star step_f_init n' tr ->
      raft_intermediate_reachable (snd n').
  Proof.
    intros. find_apply_lem_hyp refl_trans_1n_n1_trace.
    remember step_f_init as net1.
    induction H.
    - subst. simpl. constructor.
    - destruct x'; destruct x''. simpl in *.
      econstructor; eauto.
  Qed.

  Lemma step_f_star_raft_intermediate_reachable :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      raft_intermediate_reachable net.
  Proof.
    intros.
    replace net with (snd (failed, net)); [|simpl; auto].
    eapply step_f_star_raft_intermediate_reachable'; eauto.
  Qed.

  Definition raft_net_invariant_client_request (P : network -> Prop) :=
    forall h net st' ps' out d l client id c,
      handleClientRequest h (nwState net h) client id c = (out, d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h d h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_timeout (P : network -> Prop) :=
    forall net h st' ps' out d l,
      handleTimeout h (nwState net h) = (out, d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h d h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                               In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_append_entries (P : network -> Prop) :=
    forall xs p ys net st' ps' d m t n pli plt es ci,
      handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (d, m) ->
      pBody p = AppendEntries t n pli plt es ci ->
      P net ->
      raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_append_entries_reply (P : network -> Prop) :=
    forall xs p ys net st' ps' d m t es res,
      handleAppendEntriesReply (pDst p) (nwState net (pDst p)) (pSrc p) t es res = (d, m) ->
      pBody p = AppendEntriesReply t es res ->
      P net ->
      raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         In p' (send_packets (pDst p) m)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_request_vote (P : network -> Prop) :=
    forall xs p ys net st' ps' d m t cid lli llt,
      handleRequestVote (pDst p) (nwState net (pDst p)) t (pSrc p) lli llt  = (d, m) ->
      pBody p = RequestVote t cid lli llt ->
      P net ->
      raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_request_vote_reply (P : network -> Prop) :=
    forall xs p ys net st' ps' d t v,
      handleRequestVoteReply (pDst p) (nwState net (pDst p)) (pSrc p) t v = d ->
      pBody p = RequestVoteReply t v ->
      P net ->
      raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_do_leader (P : network -> Prop) :=
    forall net st' ps' d h os d' ms,
      doLeader d h = (os, d', ms) ->
      P net ->
      raft_intermediate_reachable net ->
      nwState net h = d ->
      (forall h', st' h' = update (nwState net) h d' h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_do_generic_server (P : network -> Prop) :=
    forall net st' ps' d os d' ms h,
      doGenericServer h d = (os, d', ms) ->
      P net ->
      raft_intermediate_reachable net ->
      nwState net h = d ->
      (forall h', st' h' = update (nwState net) h d' h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Lemma raft_invariant_handle_message P :
    forall xs p ys net st' ps' d l,
      raft_net_invariant_append_entries P ->
      raft_net_invariant_append_entries_reply P ->
      raft_net_invariant_request_vote P ->
      raft_net_invariant_request_vote_reply P ->
      handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop raft_net_invariant_request_vote|
     eapply_prop raft_net_invariant_request_vote_reply|
     eapply_prop raft_net_invariant_append_entries|
     eapply_prop raft_net_invariant_append_entries_reply]; eauto;
    unfold send_packets in *; simpl in *; intros; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma raft_invariant_handle_input P :
    forall h inp net st' ps' out d l,
      raft_net_invariant_timeout P ->
      raft_net_invariant_client_request P ->
      handleInput h inp (nwState net h) = (out, d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h d h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop raft_net_invariant_timeout|
     eapply_prop raft_net_invariant_client_request]; eauto;
    unfold send_packets in *; simpl in *; intros; find_apply_hyp_hyp; intuition.
  Qed.

  Definition raft_net_invariant_state_same_packet_subset (P : network -> Prop) :=
    forall net net',
      (forall h, nwState net h = nwState net' h) ->
      (forall p, In p (nwPackets net') -> In p (nwPackets net)) ->
      P net ->
      raft_intermediate_reachable net ->
      P net'.

  Definition raft_net_invariant_reboot (P : network -> Prop) :=
    forall net net' d h d',
      reboot d = d' ->
      P net ->
      raft_intermediate_reachable net ->
      nwState net h = d ->
      (forall h', nwState net' h' = update (nwState net) h d' h') ->
      nwPackets net = nwPackets net' ->
      P net'.

  Definition raft_net_invariant_init (P : network -> Prop) :=
    P step_m_init.
  
  Theorem raft_net_invariant :
    forall P net,
      raft_net_invariant_init P ->
      raft_net_invariant_client_request P ->
      raft_net_invariant_timeout P ->
      raft_net_invariant_append_entries P ->
      raft_net_invariant_append_entries_reply P ->
      raft_net_invariant_request_vote P ->
      raft_net_invariant_request_vote_reply P ->
      raft_net_invariant_do_leader P ->
      raft_net_invariant_do_generic_server P ->
      raft_net_invariant_state_same_packet_subset P ->
      raft_net_invariant_reboot P ->
      raft_intermediate_reachable net ->
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       + unfold RaftNetHandler in *. repeat break_let.
         repeat find_inversion.
         assert
           (raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++ (send_packets (pDst p) l0);
                nwState := update (nwState net) (pDst p) r
              |}) by (eapply RIR_handleMessage; eauto; in_crush).
         assert
           (raft_intermediate_reachable
              {|
                nwPackets := ((xs ++ ys) ++ (send_packets (pDst p) l0)) ++
                                (send_packets (pDst p) l1) ;
                nwState := (update (update (nwState net) (pDst p) r) (pDst p) r0)
              |}) by (eapply RIR_doGenericServer; eauto;
                      [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop raft_net_invariant_do_leader. eauto. 
         eapply_prop raft_net_invariant_do_generic_server. eauto.
         eapply raft_invariant_handle_message with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or. auto.
         simpl. break_if; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. in_crush.
       + unfold RaftInputHandler in *. repeat break_let.
         repeat find_inversion.
         assert
           (raft_intermediate_reachable
              {|
                nwPackets := nwPackets net ++ send_packets h l0;
                nwState := update (nwState net) h r |})
           by (eapply RIR_handleInput; eauto; in_crush).
         assert
           (raft_intermediate_reachable
              {|
                nwPackets := ((nwPackets net ++ send_packets h l0) ++ send_packets h l2) ;
                nwState := update (update (nwState net) h r) h r0
              |})  by (eapply RIR_doGenericServer; eauto;
                       [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop raft_net_invariant_do_leader. eauto.
         eapply_prop raft_net_invariant_do_generic_server. eauto.
         eapply raft_invariant_handle_input with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or.
         auto.
         simpl. break_if; congruence.
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
         eapply_prop raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end. 
         eapply_prop raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop raft_net_invariant_reboot; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
    - eapply raft_invariant_handle_input; eauto.
    - eapply raft_invariant_handle_message; eauto.
    - eapply_prop raft_net_invariant_do_leader; eauto.
    - eapply_prop raft_net_invariant_do_generic_server; eauto.
  Qed.
  
End Raft.

Notation currentTerm         := (RaftState.currentTerm term name entry logIndex serverType data output).
Notation votedFor            := (RaftState.votedFor term name entry logIndex serverType data output).
Notation leaderId            := (RaftState.leaderId term name entry logIndex serverType data output).
Notation log                 := (RaftState.log term name entry logIndex serverType data output).
Notation commitIndex         := (RaftState.commitIndex term name entry logIndex serverType data output).
Notation lastApplied         := (RaftState.lastApplied term name entry logIndex serverType data output).
Notation nextIndex           := (RaftState.nextIndex term name entry logIndex serverType data output).
Notation matchIndex          := (RaftState.matchIndex term name entry logIndex serverType data output).
Notation shouldSend          := (RaftState.shouldSend term name entry logIndex serverType data output).
Notation votesReceived       := (RaftState.votesReceived term name entry logIndex serverType data output).
Notation type                := (RaftState.type term name entry logIndex serverType data output).
Notation clientCache := (RaftState.clientCache term name entry logIndex serverType data output).
Notation stateMachine := (RaftState.stateMachine term name entry logIndex serverType data output).
Notation electoralVictories := (RaftState.electoralVictories term name entry logIndex serverType data output).
Notation mkRaft_data              := (RaftState.mkRaft_data term name entry logIndex serverType data output).

Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 5 (@FailureParams _ _) => apply failure_params : typeclass_instances.
