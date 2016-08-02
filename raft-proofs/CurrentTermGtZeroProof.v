Require Import Raft.
Require Import SpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import CurrentTermGtZeroInterface.

Section CurrentTermGtZero.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma current_term_gt_zero_init :
    raft_net_invariant_init current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_init, current_term_gt_zero.
    intros. simpl in *. congruence.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma current_term_gt_zero_client_request :
    raft_net_invariant_client_request current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_client_request, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp handleClientRequest_type. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_timeout :
    raft_net_invariant_timeout current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_timeout, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp handleTimeout_type_strong. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_append_entries :
    raft_net_invariant_append_entries current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_append_entries, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp handleAppendEntries_type. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_append_entries_reply :
    raft_net_invariant_append_entries_reply current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_append_entries_reply, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp handleAppendEntriesReply_type. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_request_vote :
    raft_net_invariant_request_vote current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_request_vote, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp handleRequestVote_type. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_request_vote_reply :
    raft_net_invariant_request_vote_reply current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_request_vote_reply, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite.
    find_apply_lem_hyp handleRequestVoteReply_type. update_destruct; subst; rewrite_update.
    - intuition; repeat find_rewrite.
      + auto.
      + apply H1. find_rewrite. discriminate.
    - auto.
  Qed.

  Lemma current_term_gt_zero_do_leader :
    raft_net_invariant_do_leader current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_do_leader, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp doLeader_type. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_do_generic_server :
    raft_net_invariant_do_generic_server current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_do_generic_server, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp doGenericServer_type. intuition.
      repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma current_term_gt_zero_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, current_term_gt_zero.
    simpl. intuition. find_reverse_higher_order_rewrite. auto.
  Qed.

  Lemma current_term_gt_zero_reboot :
    raft_net_invariant_reboot current_term_gt_zero.
  Proof.
    unfold raft_net_invariant_reboot, current_term_gt_zero.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - unfold reboot in *. simpl in *. congruence.
    - auto.
  Qed.

  Lemma current_term_gt_zero_invariant :
    forall net,
      raft_intermediate_reachable net ->
      current_term_gt_zero net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply current_term_gt_zero_init.
    - apply current_term_gt_zero_client_request.
    - apply current_term_gt_zero_timeout.
    - apply current_term_gt_zero_append_entries.
    - apply current_term_gt_zero_append_entries_reply.
    - apply current_term_gt_zero_request_vote.
    - apply current_term_gt_zero_request_vote_reply.
    - apply current_term_gt_zero_do_leader.
    - apply current_term_gt_zero_do_generic_server.
    - apply current_term_gt_zero_state_same_packet_subset.
    - apply current_term_gt_zero_reboot.
  Qed.

  Instance ctgzi : current_term_gt_zero_interface.
  Proof.
    split. apply current_term_gt_zero_invariant.
  Qed.
End CurrentTermGtZero.
