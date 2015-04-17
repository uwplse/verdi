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

  Theorem handleAppendEntries_log_detailed :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (commitIndex st' = commitIndex st /\ log st' = log st) \/
      (commitIndex st' = max (commitIndex st) (min ci (maxIndex es)) /\
       es <> nil /\
       pli = 0 /\ t >= currentTerm st /\ log st' = es /\
       (findAtIndex (log st) (maxIndex es) = None \/
        exists e,
          findAtIndex (log st) (maxIndex es) = Some e /\
          eTerm e <> maxTerm es)) \/
      (commitIndex st' = max (commitIndex st)
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
        simpl in *; intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex|].
    break_match; [|find_inversion; subst; eauto].
    break_if; [find_inversion; subst; eauto|].
    break_if; [|find_inversion; subst; eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex].
    find_inversion; subst; simpl in *.
    right. right.
    find_apply_lem_hyp findAtIndex_elim.
    intuition; do_bool; find_apply_lem_hyp haveNewEntries_true;
    intuition eauto.
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

  Lemma handleAppendEntriesReply_type :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      (type st' = type st /\ currentTerm st' = currentTerm st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
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
      st' = handleRequestVoteReply h st h' t r ->
      log st' = log st.
  Proof.
    intros.
    eapply handleRequestVoteReply_spec; eauto.
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

End SpecLemmas.
