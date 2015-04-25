Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Omega.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import TermSanityInterface.
Require Import CandidateTermGtLogInterface.

Section CandidateTermGtLog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {tsi : term_sanity_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma candidate_term_gt_log_init :
    raft_net_invariant_init candidate_term_gt_log.
  Proof.
    red. unfold candidate_term_gt_log. simpl. discriminate.
  Qed.

  Lemma candidate_term_gt_log_client_request :
    raft_net_invariant_client_request candidate_term_gt_log.
  Proof.
    red. unfold candidate_term_gt_log. simpl. intros.
    find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_copy_apply_lem_hyp handleClientRequest_type.
    find_apply_lem_hyp handleClientRequest_log. intuition.
    + repeat find_rewrite. eauto.
    + break_exists. intuition. repeat find_rewrite. discriminate.
  Qed.

  Lemma candidate_term_gt_log_timeout :
    raft_net_invariant_timeout candidate_term_gt_log.
  Proof.
    red. unfold candidate_term_gt_log. simpl. intros.
    find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    find_copy_apply_lem_hyp handleTimeout_log_same.
    find_apply_lem_hyp handleTimeout_type_strong. intuition.
    + repeat find_rewrite. eauto.
    + find_apply_lem_hyp no_entries_past_current_term_invariant.
      unfold no_entries_past_current_term in *. intuition.
      unfold no_entries_past_current_term_host in *. repeat find_rewrite.
      find_apply_hyp_hyp. omega.
  Qed.

  Lemma candidate_term_gt_log_append_entries :
    raft_net_invariant_append_entries candidate_term_gt_log.
  Proof.
    red. unfold candidate_term_gt_log. simpl. intros.
    find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
    unfold handleAppendEntries in *. repeat break_match; tuple_inversion; eauto; discriminate.
  Qed.

  Ltac start := red; unfold candidate_term_gt_log; simpl; intros;
    find_higher_order_rewrite; update_destruct; subst; rewrite_update; [|auto].

  Lemma candidate_term_gt_log_append_entries_reply :
    raft_net_invariant_append_entries_reply candidate_term_gt_log.
  Proof.
    start.
    find_copy_apply_lem_hyp handleAppendEntriesReply_type.
    find_copy_apply_lem_hyp handleAppendEntriesReply_log.
    intuition; repeat find_rewrite; [eauto|discriminate].
  Qed.

  Lemma candidate_term_gt_log_request_vote :
    raft_net_invariant_request_vote candidate_term_gt_log.
  Proof.
    start.
    find_copy_apply_lem_hyp handleRequestVote_type.
    find_copy_apply_lem_hyp handleRequestVote_log.
    intuition; repeat find_rewrite; [eauto|discriminate].
  Qed.

  Lemma candidate_term_gt_log_request_vote_reply :
    raft_net_invariant_request_vote_reply candidate_term_gt_log.
  Proof.
    red; unfold candidate_term_gt_log; simpl; intros;
      find_higher_order_rewrite; update_destruct; rewrite_update; auto.
    find_copy_apply_lem_hyp handleRequestVoteReply_type.
    find_copy_apply_lem_hyp handleRequestVoteReply_log.
    intuition; repeat find_rewrite; [eauto|discriminate|discriminate].
  Qed.

  Lemma candidate_term_gt_log_do_leader :
    raft_net_invariant_do_leader candidate_term_gt_log.
  Proof.
    start.
    find_copy_apply_lem_hyp doLeader_type.
    find_copy_apply_lem_hyp doLeader_log.
    intuition. repeat find_rewrite. eauto.
  Qed.

  Lemma candidate_term_gt_log_do_generic_server :
    raft_net_invariant_do_generic_server candidate_term_gt_log.
  Proof.
    start.
    find_copy_apply_lem_hyp doGenericServer_type.
    find_copy_apply_lem_hyp doGenericServer_log.
    intuition. repeat find_rewrite. eauto.
  Qed.

  Lemma candidate_term_gt_log_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset candidate_term_gt_log.
  Proof.
    red. unfold candidate_term_gt_log. simpl. intros.
    repeat find_reverse_higher_order_rewrite. auto.
  Qed.

  Lemma candidate_term_gt_log_reboot :
    raft_net_invariant_reboot candidate_term_gt_log.
  Proof.
    start. unfold reboot in *. simpl in *. discriminate.
  Qed.

  Lemma candidate_term_gt_log_invariant :
    forall net,
      raft_intermediate_reachable net ->
      candidate_term_gt_log net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply candidate_term_gt_log_init.
    - apply candidate_term_gt_log_client_request.
    - apply candidate_term_gt_log_timeout.
    - apply candidate_term_gt_log_append_entries.
    - apply candidate_term_gt_log_append_entries_reply.
    - apply candidate_term_gt_log_request_vote.
    - apply candidate_term_gt_log_request_vote_reply.
    - apply candidate_term_gt_log_do_leader.
    - apply candidate_term_gt_log_do_generic_server.
    - apply candidate_term_gt_log_state_same_packet_subset.
    - apply candidate_term_gt_log_reboot.
  Qed.

  Instance ctgli : candidate_term_gt_log_interface.
  Proof.
    split. apply candidate_term_gt_log_invariant.
  Qed.
End CandidateTermGtLog.
