Require Import List.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import Raft.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AppendEntriesReplySublogInterface.

Require Import MatchIndexSanityInterface.
Require Import SortedInterface.

Section MatchIndexSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {aersi : append_entries_reply_sublog_interface}.
  Context {si : sorted_interface}.

  Lemma match_index_sanity_init :
    raft_net_invariant_init match_index_sanity.
  Proof.
    unfold raft_net_invariant_init, match_index_sanity.
    simpl.
    intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
    | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
      destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    | [ |- context [ update _ ?x _ ?y ] ] =>
      destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma match_index_sanity_client_request :
    raft_net_invariant_client_request match_index_sanity.
  Proof.
    unfold raft_net_invariant_client_request, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_copy_apply_lem_hyp handleClientRequest_type.
      find_copy_apply_lem_hyp handleClientRequest_matchIndex.
      intuition.
      + repeat find_rewrite. auto.
      + repeat find_rewrite.
        destruct (name_eq_dec h0 leader).
        * subst. rewrite get_set_same_default. auto.
        * rewrite get_set_diff_default by auto.
          eauto using le_trans.
    - auto.
  Qed.

  Lemma match_index_sanity_preserved :
    forall st st',
      matchIndex_preserved st st' ->
      (forall h,
          type st = Leader ->
          assoc_default name_eq_dec (matchIndex st) h 0 <=
          maxIndex (log st)) ->
      (forall h,
          type st' = Leader ->
          assoc_default name_eq_dec (matchIndex st') h 0 <=
          maxIndex (log st')).
  Proof.
    unfold matchIndex_preserved.
    intros. intuition.
    repeat find_rewrite.
    auto.
  Qed.

  Lemma match_index_sanity_timeout :
    raft_net_invariant_timeout match_index_sanity.
  Proof.
    unfold raft_net_invariant_timeout, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_apply_lem_hyp handleTimeout_matchIndex_preserved.
      eauto using match_index_sanity_preserved.
    - auto.
  Qed.

  Lemma match_index_sanity_append_entries :
    raft_net_invariant_append_entries match_index_sanity.
  Proof.
    unfold raft_net_invariant_append_entries, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_apply_lem_hyp handleAppendEntries_matchIndex_preserved.
      eauto using match_index_sanity_preserved.
    - auto.
  Qed.

  Lemma handleAppendEntriesReply_matchIndex :
    forall h st st' m t es res h',
      handleAppendEntriesReply h st h' t es res = (st', m) ->
      type st' = Leader ->
      type st = Leader /\
      (matchIndex st' = matchIndex st \/
       res = true /\
       currentTerm st = t /\
      matchIndex st' =
      (assoc_set name_eq_dec (matchIndex st) h'
                 (Nat.max (assoc_default name_eq_dec (matchIndex st) h' 0)
                          (maxIndex es)))).
  Proof.
    unfold handleAppendEntriesReply, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; do_bool; auto.
  Qed.

  Lemma match_index_sanity_append_entries_reply :
    raft_net_invariant_append_entries_reply match_index_sanity.
  Proof.
    unfold raft_net_invariant_append_entries_reply, match_index_sanity.
    simpl. intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - erewrite handleAppendEntriesReply_log by eauto.
      find_copy_apply_lem_hyp handleAppendEntriesReply_matchIndex; auto.
      intuition.
      + repeat find_rewrite. auto.
      + repeat find_rewrite.
        destruct (name_eq_dec h (pSrc p)).
        * subst. rewrite get_set_same_default.
          apply Max.max_case; auto.
          { destruct es; simpl.
            * omega.
            * pose proof append_entries_reply_sublog_invariant _ ltac:(eauto).
              unfold append_entries_reply_sublog in *.
              eapply_prop_hyp pBody pBody; simpl; eauto.
              apply maxIndex_is_max; auto.
              apply logs_sorted_invariant; auto.
          }
        * rewrite get_set_diff_default by auto.
          auto.
    - auto.
  Qed.

  Lemma match_index_sanity_request_vote :
    raft_net_invariant_request_vote match_index_sanity.
  Proof.
    unfold raft_net_invariant_request_vote, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_apply_lem_hyp handleRequestVote_matchIndex_preserved.
      eauto using match_index_sanity_preserved.
    - auto.
  Qed.


  Lemma handleRequestVoteReply_matchIndex :
    forall n st src t v,
      type (handleRequestVoteReply n st src t v) = Leader ->
      type st = Leader /\
      matchIndex (handleRequestVoteReply n st src t v) =
      matchIndex st \/
      matchIndex (handleRequestVoteReply n st src t v) =
      (assoc_set name_eq_dec nil n (maxIndex (log st))).
  Proof.
    unfold handleRequestVoteReply, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; auto; simpl in *; try congruence.
  Qed.

  Lemma match_index_sanity_request_vote_reply :
    raft_net_invariant_request_vote_reply match_index_sanity.
  Proof.
    unfold raft_net_invariant_request_vote_reply, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - pose proof handleRequestVoteReply_matchIndex (pDst p) (nwState net (pDst p)) (pSrc p) t v.
      erewrite handleRequestVoteReply_log by eauto.
      intuition.
      + repeat find_rewrite. auto.
      + repeat find_rewrite.
        destruct (name_eq_dec h (pDst p)).
        * subst. rewrite get_set_same_default. auto.
        * rewrite get_set_diff_default by auto.
          unfold assoc_default. simpl. omega.
    - auto.
  Qed.

  Lemma match_index_sanity_do_leader :
    raft_net_invariant_do_leader match_index_sanity.
  Proof.
    unfold raft_net_invariant_do_leader, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_apply_lem_hyp doLeader_matchIndex_preserved.
      eauto using match_index_sanity_preserved.
    - auto.
  Qed.

  Lemma match_index_sanity_do_generic_server :
    raft_net_invariant_do_generic_server match_index_sanity.
  Proof.
    unfold raft_net_invariant_do_generic_server, match_index_sanity.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - find_apply_lem_hyp doGenericServer_matchIndex_preserved.
      eauto using match_index_sanity_preserved.
    - auto.
  Qed.

  Lemma match_index_sanity_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset match_index_sanity.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, match_index_sanity.
    simpl. intros.
    repeat find_reverse_higher_order_rewrite.
    auto.
  Qed.

  Lemma match_index_sanity_reboot :
    raft_net_invariant_reboot match_index_sanity.
  Proof.
    unfold raft_net_invariant_reboot, match_index_sanity, reboot.
    simpl.
    intros.
    subst.
    repeat find_higher_order_rewrite.
    update_destruct.
    - unfold assoc_default. simpl. omega.
    - auto.
  Qed.

  Lemma match_index_sanity_invariant :
    forall net,
      raft_intermediate_reachable net ->
      match_index_sanity net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply match_index_sanity_init.
    - apply match_index_sanity_client_request.
    - apply match_index_sanity_timeout.
    - apply match_index_sanity_append_entries.
    - apply match_index_sanity_append_entries_reply.
    - apply match_index_sanity_request_vote.
    - apply match_index_sanity_request_vote_reply.
    - apply match_index_sanity_do_leader.
    - apply match_index_sanity_do_generic_server.
    - apply match_index_sanity_state_same_packet_subset.
    - apply match_index_sanity_reboot.
  Qed.
  Instance matchisi : match_index_sanity_interface.
  Proof.
    split.
    exact match_index_sanity_invariant.
  Qed.
End MatchIndexSanity.
