Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import TermsAndIndicesFromOneLogInterface.
Require Import CurrentTermGtZeroInterface.

Section TermsAndIndicesFromOneLog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {ctgzi : current_term_gt_zero_interface}.

  Lemma terms_and_indices_from_one_log_init :
    raft_net_invariant_init terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_init, terms_and_indices_from_one_log.
    unfold terms_and_indices_from_one. simpl. contradiction.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma terms_and_indices_from_one_log_client_request :
    raft_net_invariant_client_request terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_client_request, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update.
    - find_apply_lem_hyp handleClientRequest_log. intuition.
      + repeat find_rewrite. auto.
      + break_exists. intuition. unfold terms_and_indices_from_one in *.
        intros. repeat find_rewrite. simpl in *. break_or_hyp.
        * intuition. find_apply_lem_hyp current_term_gt_zero_invariant.
          find_rewrite. eapply_prop current_term_gt_zero. congruence.
        * eauto.
    - auto.
  Qed.

  Lemma terms_and_indices_from_one_log_timeout :
    raft_net_invariant_timeout terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_timeout, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_apply_lem_hyp handleTimeout_log_same. find_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_append_entries :
    raft_net_invariant_append_entries terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_append_entries, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_apply_lem_hyp handleAppendEntries_log. intuition.
    - find_rewrite. auto.
    - subst. unfold terms_and_indices_from_one. admit.
    - break_exists. intuition. subst. unfold terms_and_indices_from_one in *.
      intros. find_rewrite. admit.
  Qed.

  Lemma terms_and_indices_from_one_log_append_entries_reply :
    raft_net_invariant_append_entries_reply terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_append_entries_reply, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_apply_lem_hyp handleAppendEntriesReply_log. find_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_request_vote :
    raft_net_invariant_request_vote terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_request_vote, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_apply_lem_hyp handleRequestVote_log. find_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_request_vote_reply :
    raft_net_invariant_request_vote_reply terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_request_vote_reply, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; rewrite_update; auto.
    symmetry in H. find_apply_lem_hyp handleRequestVoteReply_log. subst. find_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_do_leader :
    raft_net_invariant_do_leader terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_do_leader, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_apply_lem_hyp doLeader_log. find_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_do_generic_server :
    raft_net_invariant_do_generic_server terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_do_generic_server, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_apply_lem_hyp doGenericServer_log. find_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, terms_and_indices_from_one_log.
    simpl. intuition. find_reverse_higher_order_rewrite. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_reboot :
    raft_net_invariant_reboot terms_and_indices_from_one_log.
  Proof.
    unfold raft_net_invariant_reboot, terms_and_indices_from_one_log.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    unfold reboot. simpl. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_invariant :
    forall net,
      raft_intermediate_reachable net ->
      terms_and_indices_from_one_log net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply terms_and_indices_from_one_log_init.
    - apply terms_and_indices_from_one_log_client_request.
    - apply terms_and_indices_from_one_log_timeout.
    - apply terms_and_indices_from_one_log_append_entries.
    - apply terms_and_indices_from_one_log_append_entries_reply.
    - apply terms_and_indices_from_one_log_request_vote.
    - apply terms_and_indices_from_one_log_request_vote_reply.
    - apply terms_and_indices_from_one_log_do_leader.
    - apply terms_and_indices_from_one_log_do_generic_server.
    - apply terms_and_indices_from_one_log_state_same_packet_subset.
    - apply terms_and_indices_from_one_log_reboot.
  Qed.

  Instance taifoli : terms_and_indices_from_one_log_interface.
  Proof.
    split. apply terms_and_indices_from_one_log_invariant.
  Qed.
End TermsAndIndicesFromOneLog.
