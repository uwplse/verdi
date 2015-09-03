Require Import List.
Import ListNotations.

Require Import Arith.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import AppendEntriesReplySublogInterface.
Require Import SortedInterface.

Require Import NextIndexSafetyInterface.

Section NextIndexSafety.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {aersi : append_entries_reply_sublog_interface}.
  Context {si : sorted_interface}.

  Lemma nextIndex_safety_init :
    raft_net_invariant_init nextIndex_safety.
  Proof.
    unfold raft_net_invariant_init, nextIndex_safety.
    intros.
    discriminate.
  Qed.

  Definition nextIndex_preserved st st' :=
    (type st' = Leader ->
     type st = Leader /\
     maxIndex (log st) <= maxIndex (log st') /\
     nextIndex st' = nextIndex st).

  Lemma nextIndex_safety_preserved :
    forall st st',
      (forall h',
          type st = Leader ->
          Nat.pred (getNextIndex st h') <= maxIndex (log st)) ->
      nextIndex_preserved st st' ->
      (forall h',
          type st' = Leader ->
          Nat.pred (getNextIndex st' h') <= maxIndex (log st')).
  Proof.
    unfold getNextIndex, nextIndex_preserved in *.
    intuition.
    repeat find_rewrite.
    auto.
    unfold assoc_default in *.
    specialize (H h').
    break_match.
    - eauto using le_trans.
    - omega.
  Qed.

  Ltac update_destruct :=
    match goal with
    | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
      destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    | [ |- context [ update _ ?x _ ?y ] ] =>
      destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Theorem handleClientRequest_nextIndex_preserved :
    forall h st client id c out st' ps,
      handleClientRequest h st client id c = (out, st', ps) ->
      nextIndex_preserved st st'.
  Proof.
    unfold handleClientRequest, nextIndex_preserved.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; try congruence.
    intuition.
  Qed.

  Lemma nextIndex_safety_client_request :
    raft_net_invariant_client_request nextIndex_safety.
  Proof.
    unfold raft_net_invariant_client_request, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - eauto using nextIndex_safety_preserved, handleClientRequest_nextIndex_preserved.
    - auto.
  Qed.

  Lemma handleTimeout_nextIndex_preserved :
    forall h d out d' l,
      handleTimeout h d = (out, d', l) ->
      nextIndex_preserved d d'.
  Proof.
    unfold handleTimeout, tryToBecomeLeader, nextIndex_preserved.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; try congruence.
    auto.
  Qed.

  Lemma nextIndex_safety_timeout :
    raft_net_invariant_timeout nextIndex_safety.
  Proof.
    unfold raft_net_invariant_timeout, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - eauto using nextIndex_safety_preserved, handleTimeout_nextIndex_preserved.
    - auto.
  Qed.

  Lemma handleAppendEntries_nextIndex_preserved :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      nextIndex_preserved st st'.
  Proof.
    unfold handleAppendEntries, nextIndex_preserved, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; try congruence; auto.
  Qed.

  Lemma nextIndex_safety_append_entries :
    raft_net_invariant_append_entries nextIndex_safety.
  Proof.
    unfold raft_net_invariant_append_entries, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - eauto using nextIndex_safety_preserved, handleAppendEntries_nextIndex_preserved.
    - auto.
  Qed.

  Lemma handleAppendEntriesReply_nextIndex :
    forall h st st' m t es res h',
      handleAppendEntriesReply h st h' t es res = (st', m) ->
      type st' = Leader ->
      type st = Leader /\
      ((nextIndex st' = nextIndex st \/
       (res = true /\
        currentTerm st = t /\
        nextIndex st' =
        (assoc_set name_eq_dec (nextIndex st) h'
                   (Nat.max (getNextIndex st h') (S (maxIndex es)))))) \/
      (res = false /\
       currentTerm st = t /\
       nextIndex st' =
        (assoc_set name_eq_dec (nextIndex st) h'
                   (pred (getNextIndex st h'))))).
  Proof.
    unfold handleAppendEntriesReply, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; do_bool; simpl in *; intuition.
  Qed.


  Lemma nextIndex_safety_append_entries_reply :
    raft_net_invariant_append_entries_reply nextIndex_safety.
  Proof.
    unfold raft_net_invariant_append_entries_reply, nextIndex_safety, getNextIndex.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - erewrite handleAppendEntriesReply_log by eauto.
      find_copy_apply_lem_hyp handleAppendEntriesReply_nextIndex; auto.
      intuition; repeat find_rewrite.
      + auto.
      + destruct (name_eq_dec h' (pSrc p)).
        * subst. rewrite get_set_same_default.
          unfold getNextIndex.
          apply Max.max_case; auto.
          { destruct es; simpl.
            * omega.
            * pose proof append_entries_reply_sublog_invariant _ $(eauto)$.
              unfold append_entries_reply_sublog in *.
              eapply_prop_hyp pBody pBody; simpl; eauto.
              apply maxIndex_is_max; auto.
              apply logs_sorted_invariant; auto.
          }
        * rewrite get_set_diff_default by auto.
          auto.
      + destruct (name_eq_dec h' (pSrc p)).
        * subst. rewrite get_set_same_default.
          unfold getNextIndex.
          apply NPeano.Nat.le_le_pred.
          auto.
        * rewrite get_set_diff_default by auto.
          auto.
    - auto.
  Qed.

  Lemma handleRequestVote_nextIndex_preserved :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      nextIndex_preserved st st'.
  Proof.
    unfold handleRequestVote, nextIndex_preserved, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma nextIndex_safety_request_vote :
    raft_net_invariant_request_vote nextIndex_safety.
  Proof.
    unfold raft_net_invariant_request_vote, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - eauto using nextIndex_safety_preserved, handleRequestVote_nextIndex_preserved.
    - auto.
  Qed.

  Lemma handleRequestVoteReply_matchIndex :
    forall n st src t v,
      type (handleRequestVoteReply n st src t v) = Leader ->
      type st = Leader /\
      nextIndex (handleRequestVoteReply n st src t v) =
      nextIndex st \/
      nextIndex (handleRequestVoteReply n st src t v) = [].
  Proof.
    unfold handleRequestVoteReply.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma nextIndex_safety_request_vote_reply :
    raft_net_invariant_request_vote_reply nextIndex_safety.
  Proof.
    unfold raft_net_invariant_request_vote_reply, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_copy_apply_lem_hyp handleRequestVoteReply_matchIndex.
      unfold getNextIndex in *.
      erewrite handleRequestVoteReply_log in * by eauto.
      intuition; repeat find_rewrite.
      + auto.
      + unfold assoc_default. simpl.
        auto using NPeano.Nat.le_le_pred.
    - auto.
  Qed.

  Lemma doLeader_nextIndex_preserved :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      nextIndex_preserved st st'.
  Proof.
    unfold doLeader, nextIndex_preserved.
    intros.
    repeat break_match; repeat find_inversion; auto; try congruence.
  Qed.

  Lemma nextIndex_safety_do_leader :
    raft_net_invariant_do_leader nextIndex_safety.
  Proof.
    unfold raft_net_invariant_do_leader, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - eauto using nextIndex_safety_preserved, doLeader_nextIndex_preserved.
    - auto.
  Qed.

  Lemma doGenericServer_nextIndex_preserved :
    forall h st os st' ms,
      doGenericServer h st = (os, st', ms) ->
      nextIndex_preserved st st'.
  Proof.
    unfold doGenericServer, nextIndex_preserved.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence;
    use_applyEntries_spec; subst; simpl in *; auto.
  Qed.

  Lemma nextIndex_safety_do_generic_server :
    raft_net_invariant_do_generic_server nextIndex_safety.
  Proof.
    unfold raft_net_invariant_do_generic_server, nextIndex_safety.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - eauto using nextIndex_safety_preserved, doGenericServer_nextIndex_preserved.
    - auto.
  Qed.

  Lemma nextIndex_safety_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset nextIndex_safety.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, nextIndex_safety.
    simpl.
    intros.
    repeat find_reverse_higher_order_rewrite.
    auto.
  Qed.

  Lemma nextIndex_safety_reboot :
    raft_net_invariant_reboot nextIndex_safety.
  Proof.
    unfold raft_net_invariant_reboot, nextIndex_safety, reboot.
    simpl.
    intros.
    subst.
    repeat find_higher_order_rewrite.
    update_destruct.
    - unfold getNextIndex, assoc_default. simpl. omega.
    - auto.
  Qed.

  Lemma nextIndex_safety_invariant :
    forall net,
      raft_intermediate_reachable net ->
      nextIndex_safety net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply nextIndex_safety_init.
    - apply nextIndex_safety_client_request.
    - apply nextIndex_safety_timeout.
    - apply nextIndex_safety_append_entries.
    - apply nextIndex_safety_append_entries_reply.
    - apply nextIndex_safety_request_vote.
    - apply nextIndex_safety_request_vote_reply.
    - apply nextIndex_safety_do_leader.
    - apply nextIndex_safety_do_generic_server.
    - apply nextIndex_safety_state_same_packet_subset.
    - apply nextIndex_safety_reboot.
  Qed.

  Instance nisi : nextIndex_safety_interface.
  Proof.
    split.
    exact nextIndex_safety_invariant.
  Qed.
End NextIndexSafety.
