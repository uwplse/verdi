Require Import List.
Import ListNotations.
Require Import Min.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonTheorems.

Section SpecLemmas.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Theorem handleAppendEntries_log :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      log st' = log st \/
      log st' = es \/
      (exists e,
         In e (log st) /\
         eIndex e = pli /\
         eTerm e = plt) /\
      log st' = es ++ (removeAfterIndex (log st) pli).
  Proof.
    intros. unfold handleAppendEntries in *.
    break_if; [find_inversion; subst; eauto|].
    break_if; [do_bool; break_if; find_inversion; subst; eauto|].
    break_if.
    - break_match; [|find_inversion; subst; eauto].
      break_if; [find_inversion; subst; eauto|].
      find_inversion; subst; simpl in *.
      right. right.
      find_apply_lem_hyp findAtIndex_elim. intuition.
      do_bool. eauto.
    - repeat break_match; find_inversion; subst; eauto.
  Qed.

  Theorem handleAppendEntries_log_ind :
    forall {h st t n pli plt es ci st' ps},
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      forall (P : list entry -> Prop),
        P (log st) ->
        P es ->
        (forall e,
           In e (log st) ->
           eIndex e = pli ->
           eTerm e = plt ->
           P (es ++ (removeAfterIndex (log st) pli))) ->
        P (log st').
  Proof.
    intros.
    find_apply_lem_hyp handleAppendEntries_log.
    intuition; find_rewrite; auto.
    break_exists. intuition eauto.
  Qed.
  
  Theorem handleAppendEntries_spec :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (currentTerm st <= currentTerm st' /\
       (commitIndex st' = commitIndex st \/ commitIndex st' <= ci) /\
       (lastApplied st' = lastApplied st) /\
       (log st' = log st \/
        log st' = es \/
        (exists e,
           In e (log st) /\
           eIndex e = pli /\
           eTerm e = plt) /\
        log st' = es ++ (removeAfterIndex (log st) pli))).
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; do_bool; find_inversion; subst; simpl in *; intuition eauto using le_min_l;
    right; right; find_apply_lem_hyp findAtIndex_elim; intuition eauto.
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
         eId e = id).
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
End SpecLemmas.
