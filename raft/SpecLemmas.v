Require Import List.
Import ListNotations.
Require Import Min.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonTheorems.

Section SpecLemmas.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma haveNewEntries_not_empty :
    forall st es,
      haveNewEntries st es = true ->
      es <> [].
  Proof.
    intros. unfold haveNewEntries, not_empty in *.
    do_bool. intuition. repeat break_match; congruence.
  Qed.

  Lemma advanceCurrentTerm_log :
    forall st t,
      log (advanceCurrentTerm st t) = log st.
  Proof.
    intros.
    unfold advanceCurrentTerm. break_if; simpl in *; auto.
  Qed.

  Theorem handleAppendEntries_log :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      log st' = log st \/
      (currentTerm st <= t /\ es <> [] /\ pli = 0 /\ log st' = es) \/
      (currentTerm st <= t /\ es <> [] /\ pli <> 0 /\ exists e,
         In e (log st) /\
         eIndex e = pli /\
         eTerm e = plt) /\
      log st' = es ++ (removeAfterIndex (log st) pli).
  Proof.
    intros. unfold handleAppendEntries in *.
    break_if; [find_inversion; subst; eauto|].
    break_if;
      [do_bool; break_if; find_inversion; subst;
       try find_apply_lem_hyp haveNewEntries_not_empty; intuition; simpl in *;
       eauto using advanceCurrentTerm_log|].
    break_if.
    - break_match; [|find_inversion; subst; eauto].
      break_if; [find_inversion; subst; eauto|].
      find_inversion; subst; simpl in *.
      right. right.
      find_apply_lem_hyp findAtIndex_elim. intuition; do_bool; eauto.
      find_apply_lem_hyp haveNewEntries_not_empty. congruence.
    - repeat break_match; find_inversion; subst; eauto.
      simpl in *. eauto using advanceCurrentTerm_log.
  Qed.

  Theorem handleAppendEntries_log_ind :
    forall {h st t n pli plt es ci st' ps},
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      forall (P : list entry -> Prop),
        P (log st) ->
        (pli = 0 -> P es) ->
        (forall e,
           pli <> 0 ->
           In e (log st) ->
           eIndex e = pli ->
           eTerm e = plt ->
           P (es ++ (removeAfterIndex (log st) pli))) ->
        P (log st').
  Proof.
    intros.
    find_apply_lem_hyp handleAppendEntries_log.
    intuition; subst; try find_rewrite; auto.
    break_exists. intuition eauto.
  Qed.

  Lemma haveNewEntries_true :
    forall st es,
      haveNewEntries st es = true ->
      (es <> nil /\
       (findAtIndex (log st) (maxIndex es) = None \/
        exists e,
          findAtIndex (log st) (maxIndex es) = Some e /\
          eTerm e <> maxTerm es)).
  Proof.
    intros.
    unfold haveNewEntries, not_empty in *.
    repeat break_match; do_bool; intuition eauto; try congruence.
    do_bool. eauto.
  Qed.

  Lemma advanceCurrentTerm_commitIndex :
    forall st t,
      commitIndex (advanceCurrentTerm st t) = commitIndex st.
  Proof.
    intros.
    unfold advanceCurrentTerm. break_if; simpl in *; auto.
  Qed.

  Lemma some_none :
    forall A (x : A),
      Some x = None -> False.
  Proof.
    congruence.
  Qed.

  Lemma advanceCurrentTerm_term :
    forall st t,
      currentTerm st <= t ->
      currentTerm (advanceCurrentTerm st t) = t.
  Proof.
    intros. unfold advanceCurrentTerm in *.
    break_if; do_bool; intuition.
  Qed.
    
  Theorem handleAppendEntries_log_detailed :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (commitIndex st' = commitIndex st /\ log st' = log st) \/
      (leaderId st' <> None /\
       currentTerm st' = t /\
       commitIndex st' = max (commitIndex st) (min ci (maxIndex es)) /\
       es <> nil /\
       pli = 0 /\ t >= currentTerm st /\ log st' = es /\
       (findAtIndex (log st) (maxIndex es) = None \/
        exists e,
          findAtIndex (log st) (maxIndex es) = Some e /\
          eTerm e <> maxTerm es)) \/
      (leaderId st' <> None /\
       currentTerm st' = t /\
       commitIndex st' = max (commitIndex st)
                             (min ci (maxIndex (es ++ (removeAfterIndex (log st) pli)))) /\
       es <> nil /\
        exists e,
         In e (log st) /\
         eIndex e = pli /\
         eTerm e = plt) /\
      t >= currentTerm st /\
      log st' = es ++ (removeAfterIndex (log st) pli) /\
      (findAtIndex (log st) (maxIndex es) = None \/
       exists e,
         findAtIndex (log st) (maxIndex es) = Some e /\
         eTerm e <> maxTerm es).
  Proof.
    intros. unfold handleAppendEntries in *.
    break_if; [find_inversion; subst; eauto|].
    break_if;
      [do_bool; break_if; find_inversion; subst;
        try find_apply_lem_hyp haveNewEntries_true;
        simpl in *; intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex, some_none, advanceCurrentTerm_term|].
    simpl in *. intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex.
    break_match; [|find_inversion; subst; eauto].
    break_if; [find_inversion; subst; eauto|].
    break_if; [|find_inversion; subst; eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex].
    find_inversion; subst; simpl in *.
    right. right.
    find_apply_lem_hyp findAtIndex_elim.
    intuition; do_bool; find_apply_lem_hyp haveNewEntries_true;
    intuition eauto using advanceCurrentTerm_term; congruence.
  Qed.

  Lemma advanceCurrentTerm_currentTerm_leaderId :
    forall st t,
      currentTerm st < currentTerm (advanceCurrentTerm st t) \/
      leaderId (advanceCurrentTerm st t) = leaderId st.
  Proof.
    intros.
    unfold advanceCurrentTerm in *.
    break_if; simpl in *; do_bool; auto.
  Qed.

  
  Lemma advanceCurrentTerm_currentTerm :
    forall st t,
      currentTerm st <= currentTerm (advanceCurrentTerm st t).
  Proof.
    intros. unfold advanceCurrentTerm in *.
    break_if; simpl in *; do_bool; omega.
  Qed.

  Theorem handleAppendEntries_currentTerm_leaderId :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      currentTerm st < currentTerm st' \/
      (currentTerm st <= currentTerm st' /\ (leaderId st' = leaderId st \/ leaderId st' <> None)).
  Proof.
    intros. unfold handleAppendEntries in *.
    repeat break_match; find_inversion; simpl in *; auto; right;
    intuition eauto using advanceCurrentTerm_currentTerm; right; congruence.
  Qed.

  Lemma handleRequestVote_currentTerm_leaderId :
    forall h st t c li lt st' m,
      handleRequestVote h st t c li lt = (st', m) ->
      currentTerm st < currentTerm st' \/
      (currentTerm st = currentTerm st' /\ leaderId st' = leaderId st).
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat (break_match; try find_inversion; simpl in *; auto);
    do_bool; auto.
  Qed.
  
  Lemma handleRequestVoteReply_currentTerm_leaderId :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      currentTerm st < currentTerm st' \/
      currentTerm st' = currentTerm st /\
      leaderId st' = leaderId st.
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm in *.
    subst.
    repeat (break_match; try find_inversion; simpl in *; auto);
      do_bool; auto.
  Qed.
  
  Theorem handleClientRequest_log :
    forall h st client id c out st' ps,
      handleClientRequest h st client id c = (out, st', ps) ->
      ps = [] /\
      (log st' = log st \/
       exists e,
         log st' = e :: log st /\
         eIndex e = S (maxIndex (log st)) /\
         eTerm e = currentTerm st /\
         eClient e = client /\
         eInput e = c /\
         eId e = id /\
         type st = Leader).
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; intuition.
    simpl in *. eauto 10.
  Qed.

  Lemma handleClientRequest_log_ind :
    forall {h st client id c out st' ps},
      handleClientRequest h st client id c = (out, st', ps) ->
      forall (P : list entry -> Prop),
        P (log st) ->
        (forall e, eIndex e = S (maxIndex (log st)) ->
                   eTerm e = currentTerm st ->
                   eClient e = client ->
                   eInput e = c ->
                   eId e = id ->
                   type st = Leader ->
                   P (e :: log st)) ->
        P (log st').
  Proof.
    intros.
    find_apply_lem_hyp handleClientRequest_log.
    intuition; repeat find_rewrite; auto.
    break_exists. intuition. repeat find_rewrite. eauto.
  Qed.

  Lemma handleRequestVote_log :
    forall h st t candidate lli llt st' m,
      handleRequestVote h st t candidate lli llt = (st', m) ->
      log st' = log st.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Lemma handleTimeout_log_same :
    forall h d out d' l,
      handleTimeout h d = (out, d', l) ->
      log d' = log d.
  Proof.
    unfold handleTimeout, tryToBecomeLeader.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma doGenericServer_log :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      log st' = log st.
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion;
    use_applyEntries_spec; simpl in *;
    subst; auto.
  Qed.

  Lemma handleRequestVoteReply_spec :
    forall h st h' t r st',
      st' = handleRequestVoteReply h st h' t r ->
      log st' = log st /\
      (forall v, In v (votesReceived st) -> In v (votesReceived st')) /\
      ((currentTerm st' = currentTerm st /\ type st' = type st)
       \/ type st' <> Candidate) /\
      (type st <> Leader /\ type st' = Leader ->
       (type st = Candidate /\ wonElection (dedup name_eq_dec
                                                 (votesReceived st')) = true)).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try right; congruence.
  Qed.

  Lemma handleRequestVoteReply_spec' :
    forall h st h' t r st',
      st' = handleRequestVoteReply h st h' t r ->
      log st' = log st /\
      (forall v, In v (votesReceived st) -> In v (votesReceived st')) /\
      (type st <> Leader /\ type st' = Leader ->
       (type st = Candidate /\ wonElection (dedup name_eq_dec
                                                 (votesReceived st')) = true) /\
       r = true /\
       currentTerm st' = currentTerm st /\
       currentTerm st = t /\
       votesReceived st' = (h' :: (votesReceived st))).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try right; congruence.
  Qed.
  
  Theorem handleTimeout_not_is_append_entries :
    forall h st st' ms m,
      handleTimeout h st = (st', ms) ->
      In m ms -> ~ is_append_entries (snd m).
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; find_inversion; subst; simpl in *; eauto;
    repeat (do_in_map; subst; simpl in *); intuition; break_exists; congruence.
  Qed.


  Lemma handleAppendEntries_type :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleAppendEntries_type_term :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      (type st' = Follower /\ currentTerm st' >= currentTerm st).
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; do_bool; auto.
  Qed.

  Lemma handleAppendEntriesReply_type :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleAppendEntriesReply_type_term :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      (type st' = Follower /\ currentTerm st' >= currentTerm st).
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; tuple_inversion; do_bool; auto.
  Qed.

  Lemma handleRequestVote_type :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleRequestVote_type_term :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      (type st' = Follower /\ currentTerm st' >= currentTerm st).
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; tuple_inversion; do_bool; auto.
  Qed.

  Lemma handleRequestVoteReply_type :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      (type st' = Follower /\ currentTerm st' > currentTerm st) \/
      (type st = Candidate /\ type st' = Leader /\ currentTerm st' = currentTerm st).
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; subst; do_bool; intuition.
  Qed.

  Lemma handleClientRequest_type :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      type st' = type st /\ currentTerm st' = currentTerm st.
  Proof.
    intros. unfold handleClientRequest in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleTimeout_type :
    forall h st out st' l,
      handleTimeout h st = (out, st', l) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      type st' = Candidate.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleTimeout_type_strong :
    forall h st out st' l,
      handleTimeout h st = (out, st', l) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      (type st' = Candidate /\ currentTerm st' = S (currentTerm st)).
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; simpl; intuition.
  Qed.

  Lemma doGenericServer_type :
    forall h st os st' ms,
      doGenericServer h st = (os, st', ms) ->
      type st' = type st /\ currentTerm st' = currentTerm st.
  Proof.
    unfold doGenericServer.
    intros.
    repeat break_match; repeat find_inversion;
    use_applyEntries_spec; subst; simpl in *;
    auto.
  Qed.

  Lemma doLeader_type :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      type st' = type st /\ currentTerm st' = currentTerm st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma doLeader_log :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      log st' = log st.
  Proof.
    unfold doLeader. intros.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Lemma handleAppendEntriesReply_log :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      log st' = log st.
  Proof.
    unfold handleAppendEntriesReply, advanceCurrentTerm.
    intros.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Lemma handleRequestVoteReply_log :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      log st' = log st.
  Proof.
    intros.
    eapply handleRequestVoteReply_spec; eauto.
  Qed.

  Lemma handleRequestVoteReply_log_rewrite :
    forall h st h' t r,
      log (handleRequestVoteReply h st h' t r) = log st.
  Proof.
    intros.
    erewrite handleRequestVoteReply_log; eauto.
  Qed.

  Lemma handleAppendEntriesReply_packets :
    forall h st from t es s st' ps,
      handleAppendEntriesReply h st from t es s = (st', ps) ->
      ps = [].
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Lemma doGenericServer_packets :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      ps = [].
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion; simpl in *;
    subst; auto.
  Qed.

  Theorem handleAppendEntries_not_append_entries :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      ~ is_append_entries m.
  Proof.
    intros. unfold handleAppendEntries in *.
    repeat break_match; find_inversion;
    intuition; break_exists; congruence.
  Qed.

  Lemma handleAppendEntries_clientCache:
    forall h st (d : raft_data) 
      (m : msg) (t : term) (n : name) (pli : logIndex) 
      (plt : term) (es : list entry) (ci : logIndex),
      handleAppendEntries h st t n pli plt es ci = (d, m) ->
      clientCache d = clientCache st.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Lemma handleAppendEntriesReply_clientCache:
    forall h st (d : raft_data)
      (m : list (name * msg)) (t : nat) (es : list entry) 
      (res : bool) h',
      handleAppendEntriesReply h st h' t es res = (d, m) ->
      clientCache d = clientCache st.
  Proof.
    intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat (break_match; try find_inversion; simpl in *; auto).
  Qed.

  Lemma advanceCurrentTerm_clientCache :
    forall st t,
      clientCache (advanceCurrentTerm st t) = clientCache st.
  Proof.
    unfold advanceCurrentTerm. intros.
    break_if; auto.
  Qed.

  Theorem handleTimeout_clientCache :
    forall h st out st' ps,
      handleTimeout h st = (out, st', ps) ->
      clientCache st' = clientCache st.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; find_inversion; subst; auto.
  Qed.

  Theorem handleClientRequest_clientCache:
  forall h st client id c out st' ps,
    handleClientRequest h st client id c = (out, st', ps) ->
    clientCache st' = clientCache st.
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; auto.
  Qed.

  Lemma tryToBecomeLeader_clientCache :
    forall n st out st' ms,
      tryToBecomeLeader n st = (out, st', ms) ->
      clientCache st' = clientCache st.
  Proof.
    unfold tryToBecomeLeader.
    intros. find_inversion. auto.
  Qed.

  Lemma handleRequestVote_clientCache :
    forall n st t c li lt st' ms,
      handleRequestVote n st t c li lt = (st', ms) ->
      clientCache st' = clientCache st.
  Proof.
    unfold handleRequestVote.
    intros.
    repeat (break_match; try discriminate; repeat (find_inversion; simpl in *));
      auto using advanceCurrentTerm_clientCache.
  Qed.

  Lemma handleRequestVoteReply_clientCache :
    forall n st src t v,
      clientCache (handleRequestVoteReply n st src t v) = clientCache st.
  Proof.
    unfold handleRequestVoteReply.
    intros. repeat break_match; simpl; auto using advanceCurrentTerm_clientCache.
  Qed.

  Lemma doLeader_clientCache :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      clientCache st' = clientCache st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleAppendEntries_stateMachine:
    forall h st (d : raft_data) 
      (m : msg) (t : term) (n : name) (pli : logIndex) 
      (plt : term) (es : list entry) (ci : logIndex),
      handleAppendEntries h st t n pli plt es ci = (d, m) ->
      stateMachine d = stateMachine st.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Lemma handleAppendEntriesReply_stateMachine:
    forall h st (d : raft_data)
      (m : list (name * msg)) (t : nat) (es : list entry) 
      (res : bool) h',
      handleAppendEntriesReply h st h' t es res = (d, m) ->
      stateMachine d = stateMachine st.
  Proof.
    intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat (break_match; try find_inversion; simpl in *; auto).
  Qed.

  Lemma advanceCurrentTerm_stateMachine :
    forall st t,
      stateMachine (advanceCurrentTerm st t) = stateMachine st.
  Proof.
    unfold advanceCurrentTerm. intros.
    break_if; auto.
  Qed.

  Theorem handleTimeout_stateMachine :
    forall h st out st' ps,
      handleTimeout h st = (out, st', ps) ->
      stateMachine st' = stateMachine st.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; find_inversion; subst; auto.
  Qed.

  Theorem handleClientRequest_stateMachine:
  forall h st client id c out st' ps,
    handleClientRequest h st client id c = (out, st', ps) ->
    stateMachine st' = stateMachine st.
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; auto.
  Qed.

  Lemma tryToBecomeLeader_stateMachine :
    forall n st out st' ms,
      tryToBecomeLeader n st = (out, st', ms) ->
      stateMachine st' = stateMachine st.
  Proof.
    unfold tryToBecomeLeader.
    intros. find_inversion. auto.
  Qed.

  Lemma handleRequestVote_stateMachine :
    forall n st t c li lt st' ms,
      handleRequestVote n st t c li lt = (st', ms) ->
      stateMachine st' = stateMachine st.
  Proof.
    unfold handleRequestVote.
    intros.
    repeat (break_match; try discriminate; repeat (find_inversion; simpl in *));
      auto using advanceCurrentTerm_stateMachine.
  Qed.

  Lemma handleRequestVoteReply_stateMachine :
    forall n st src t v,
      stateMachine (handleRequestVoteReply n st src t v) = stateMachine st.
  Proof.
    unfold handleRequestVoteReply.
    intros. repeat break_match; simpl; auto using advanceCurrentTerm_stateMachine.
  Qed.

  Lemma doLeader_stateMachine :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      stateMachine st' = stateMachine st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.

(* matchIndex *)
  Definition matchIndex_preserved st st' :=
    type st' = Leader ->
    (type st = Leader /\ matchIndex st' = matchIndex st /\ log st' = log st).

  Arguments matchIndex_preserved / _ _.

  Definition matchIndex_preserved_except_at_host h st st' :=
    type st' = Leader ->
    (type st = Leader /\
     forall h',
       h <> h' ->
       (assoc_default name_eq_dec (matchIndex st') h' 0) = (assoc_default name_eq_dec (matchIndex st) h') 0).

  Arguments matchIndex_preserved_except_at_host / _ _ _.
  
  Lemma handleAppendEntries_matchIndex_preserved:
    forall h st (d : raft_data) 
      (m : msg) (t : term) (n : name) (pli : logIndex) 
      (plt : term) (es : list entry) (ci : logIndex),
      handleAppendEntries h st t n pli plt es ci = (d, m) ->
      matchIndex_preserved st d.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto; intros; congruence.
  Qed.

  Lemma handleAppendEntriesReply_matchIndex_leader_preserved:
    forall h st (d : raft_data)
      (m : list (name * msg)) (t : nat) (es : list entry) 
      (res : bool) h',
      handleAppendEntriesReply h st h' t es res = (d, m) ->
      matchIndex_preserved_except_at_host h' st d.
  Proof.
    intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat (break_match; try find_inversion; simpl in *; auto).
    intros. intuition.
    unfold assoc_default.
    repeat break_match; rewrite get_set_diff in *; repeat find_rewrite; congruence.
  Qed.

  Lemma advanceCurrentTerm_matchIndex_preserved :
    forall st t,
      matchIndex_preserved st (advanceCurrentTerm st t).
  Proof.
    unfold advanceCurrentTerm. intros.
    break_if; simpl in *; auto; congruence.
  Qed.

  Theorem handleTimeout_matchIndex_preserved :
    forall h st out st' ps,
      handleTimeout h st = (out, st', ps) ->
      matchIndex_preserved st st'.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; simpl in *; find_inversion; subst; simpl in *; auto; congruence.
  Qed.

  Theorem handleClientRequest_matchIndex_maxIndex:
  forall h st client id c out st' ps,
    handleClientRequest h st client id c = (out, st', ps) ->
    (maxIndex (log st') = maxIndex (log st) /\
     matchIndex st' = matchIndex st) \/
    (assoc_default name_eq_dec (matchIndex st') h 0) = maxIndex (log st').
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; simpl in *; auto.
    unfold assoc_default. break_match;
    rewrite get_set_same in *; try congruence; find_inversion; auto.
  Qed.

  Theorem handleClientRequest_matchIndex :
    forall h st client id c out st' ps,
      handleClientRequest h st client id c = (out, st', ps) ->
      (maxIndex (log st') = maxIndex (log st) /\
       matchIndex st' = matchIndex st) \/
      matchIndex st' = assoc_set name_eq_dec (matchIndex st) h (maxIndex (log st')) /\
      maxIndex (log st') = S (maxIndex (log st)).
  Proof.
    unfold handleClientRequest.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma tryToBecomeLeader_matchIndex_preserved :
    forall n st out st' ms,
      tryToBecomeLeader n st = (out, st', ms) ->
      matchIndex_preserved st st'.
  Proof.
    unfold tryToBecomeLeader.
    intros. find_inversion. simpl; intros; auto; congruence.
  Qed.

  Lemma handleRequestVote_matchIndex_preserved :
    forall n st t c li lt st' ms,
      handleRequestVote n st t c li lt = (st', ms) ->
      matchIndex_preserved st st'.
  Proof.
    unfold handleRequestVote, advanceCurrentTerm.
    intros.
    repeat (break_match; try discriminate; repeat (find_inversion; simpl in *)); auto.
  Qed.

  Lemma doGenericServer_matchIndex_preserved :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      matchIndex_preserved st st'.
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion;
    use_applyEntries_spec; simpl in *;
    subst; auto.
  Qed.

  Lemma handleRequestVoteReply_matchIndex :
    forall n st src t v,
      type (handleRequestVoteReply n st src t v) = Leader ->
      (type st = Leader /\ matchIndex (handleRequestVoteReply n st src t v) = matchIndex st) \/
      (assoc_default name_eq_dec (matchIndex (handleRequestVoteReply n st src t v)) n 0
       = maxIndex (log (handleRequestVoteReply n st src t v))).
  Proof.
    unfold handleRequestVoteReply.
    intros.
    repeat break_match; simpl; auto using advanceCurrentTerm_matchIndex_preserved;
    simpl in *; try congruence.
    unfold assoc_default. simpl.
    repeat break_match; simpl in *; try congruence; find_inversion; auto.
  Qed.
  
  Lemma doLeader_matchIndex_preserved :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      matchIndex_preserved st st'.
  Proof.
    intros. unfold doLeader in *. simpl; intros.
    repeat break_match; find_inversion; auto; congruence.
  Qed.
  
  Lemma doLeader_lastApplied :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      lastApplied st' = lastApplied st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.  
  Lemma handleRequestVote_no_append_entries :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      ~ is_append_entries m.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; subst; auto;
    intuition; break_exists; congruence.
  Qed.

  Theorem handleClientRequest_no_append_entries :
    forall h st client id c out st' ps m,
      handleClientRequest h st client id c = (out, st', ps) ->
      In m ps ->
      ~ is_append_entries (snd m).
  Proof.
    intros. unfold handleClientRequest in *.
    repeat break_match; find_inversion; subst; auto;
    intuition; break_exists; congruence.
  Qed.

  Theorem handleClientRequest_packets :
    forall h st client id c out st' ps,
      handleClientRequest h st client id c = (out, st', ps) ->
      ps = [].
  Proof.
    intros. unfold handleClientRequest in *.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma handleTimeout_packets :
    forall h d out d' ps m,
      handleTimeout h d = (out, d', ps) ->
      In m ps ->
      ~ is_append_entries (snd m).
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; subst; auto;
    intuition; break_exists;
    do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma doLeader_messages :
    forall st h os st' ms m t n pli plt es ci,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      t = currentTerm st /\
      log st' = log st /\
      type st = Leader /\
      ((plt = 0) \/
       ((exists e, findAtIndex (log st) pli = Some e /\
              eTerm e = plt))).
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    break_match; try solve [find_inversion; simpl in *; intuition].
    break_if; try solve [find_inversion; simpl in *; intuition].
    find_inversion. simpl. do_in_map. subst.
    simpl in *. find_inversion. intuition.
    match goal with
      | |- context [pred ?x] =>
        remember (pred x) as index
    end. break_match; simpl in *.
    - right. eauto.
    - destruct index; intuition.
  Qed.

  Lemma doLeader_message_entries :
    forall st h os st' ms m t n pli plt es ci e,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      In e es ->
      In e (log st).
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    break_match; try solve [find_inversion; simpl in *; intuition].
    break_if; try solve [find_inversion; simpl in *; intuition].
    find_inversion. simpl. do_in_map. subst.
    simpl in *. find_inversion.
    eauto using findGtIndex_in.
  Qed.


  Theorem handleAppendEntries_log_term_type :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Theorem handleAppendEntries_votesReceived :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      votesReceived st' = votesReceived st.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Theorem handleAppendEntriesReply_log_term_type :
    forall h st n t es r st' ps,
      handleAppendEntriesReply h st n t es r = (st', ps) ->
      (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Theorem handleAppendEntriesReply_votesReceived :
    forall h st n t es r st' ps,
      handleAppendEntriesReply h st n t es r = (st', ps) ->
      votesReceived st' = votesReceived st.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.


  Theorem handleRequestVote_log_term_type :
    forall h st t c li lt st' m,
      handleRequestVote h st t c li lt = (st', m) ->
      (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Theorem handleRequestVote_votesReceived :
    forall h st t c li lt st' m,
      handleRequestVote h st t c li lt = (st', m) ->
      votesReceived st' = votesReceived st.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.
  

  Theorem handleRequestVoteReply_log_term_type :
    forall h st t h' r st',
      type st' = Candidate ->
      handleRequestVoteReply h st h' t r = st' ->
      (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st).
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; subst; simpl in *; auto; congruence.
  Qed.

  Theorem handleRequestVoteReply_votesReceived :
    forall h st t h' r v,
      In v (votesReceived (handleRequestVoteReply h st h' t r)) ->
      In v (votesReceived st) \/
      (r = true /\ v = h' /\ currentTerm (handleRequestVoteReply h st h' t r) = t).
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; subst; simpl in *; do_bool; intuition.
  Qed.

  Theorem handleTimeout_log_term_type :
    forall h st out st' ps,
      handleTimeout h st = (out, st', ps) ->
      (log st' = log st /\ currentTerm st' = currentTerm st /\ type st' = type st) \/
      currentTerm st' = S (currentTerm st).
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; simpl in *; intuition.
  Qed.
  
  Lemma handleClientRequest_candidate :
    forall h st client id c os st' m,
      handleClientRequest h st client id c = (os, st', m) ->
      type st' = Candidate ->
      st' = st.
  Proof.
    intros.
    unfold handleClientRequest in *.
    repeat break_match; find_inversion; simpl in *; congruence.
  Qed.

  Lemma doLeader_candidate :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      type st' = Candidate ->
      st' = st.
  Proof.
    unfold doLeader, advanceCommitIndex in *.
    intros.
    repeat break_match; find_inversion; simpl in *; congruence.
  Qed.

  Lemma doLeader_term_votedFor :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      currentTerm st' = currentTerm st /\
      votedFor st' = votedFor st.
  Proof.
    unfold doLeader, advanceCommitIndex in *.
    intros.
    repeat break_match; find_inversion; simpl in *; intuition.
  Qed.

  Lemma doGenericServer_log_type_term_votesReceived :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      log st' = log st /\
      type st' = type st /\
      currentTerm st' = currentTerm st /\
      votesReceived st' = votesReceived st /\
      votedFor st' = votedFor st.
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion;
    use_applyEntries_spec; simpl in *;
    subst; auto.
  Qed.

  
  Lemma handleClientRequest_term_votedFor :
    forall h st client id c os st' m,
      handleClientRequest h st client id c = (os, st', m) ->
      type st' = type st /\
      currentTerm st' = currentTerm st /\
      votedFor st' = votedFor st.
  Proof.
    intros.
    unfold handleClientRequest in *.
    repeat break_match; find_inversion; simpl in *; intuition.
  Qed.


  Theorem handleAppendEntries_term_votedFor :
    forall h st t n pli plt es ci st' ps h',
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      votedFor st' = Some h' ->
      currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto; congruence.
  Qed.

  Theorem handleAppendEntriesReply_term_votedFor :
    forall h st n t es r st' ps h',
      handleAppendEntriesReply h st n t es r = (st', ps) ->
      votedFor st' = Some h' ->
      currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.

  Theorem handleRequestVoteReply_term_votedFor :
    forall h st t h' h'' r st',
      handleRequestVoteReply h st h' t r = st' ->
      votedFor st' = Some h'' ->
      currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; subst; simpl in *; auto; congruence.
  Qed.

  Lemma handleRequestVote_reply_true:
    forall h h' st t lli llt st' t',
      handleRequestVote h st t h' lli llt =
      (st', RequestVoteReply t' true) ->
      votedFor st' = Some h' /\
      currentTerm st' = t'.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *; intuition.
  Qed.

  Lemma handleTimeout_messages:
    forall (out : list raft_output) 
      (st : raft_data) (l : list (name * msg)) h
      (mi : logIndex) (mt : term) m st' t n,
      handleTimeout h st = (out, st', l) ->
      In m l ->
      snd m = RequestVote t n mi mt ->
      maxIndex (log st') = mi /\ maxTerm (log st') = mt /\ t = currentTerm st'.
  Proof.
    intros.
    unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; simpl in *; intuition;
    do_in_map; subst; simpl in *; find_inversion; auto.
  Qed.
  
  Lemma handleRequestVoteReply_currentTerm :
    forall h st h' t r x,
      x <= currentTerm st ->
      x <= currentTerm (handleRequestVoteReply h st h' t r).
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm.
    repeat break_match; subst; simpl in *; auto; try omega.
    do_bool. omega.
  Qed.

  Lemma handleRequestVote_reply_true':
  forall (h : name) 
    (h' : fin N)
    (st : RaftState.raft_data term name entry logIndex serverType data output)
    (t lli llt : nat) (st' : raft_data) (t' : term),
    handleRequestVote h st t h' lli llt = (st', RequestVoteReply t' true) ->
    t' = t /\ currentTerm st' = t.
  Proof.
    unfold handleRequestVote, advanceCurrentTerm in *.
    intros.
    repeat break_match; find_inversion; simpl in *; auto; try congruence;
    do_bool; try omega; eauto using le_antisym.
  Qed.

  
End SpecLemmas.
