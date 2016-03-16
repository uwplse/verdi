Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.
Require Import GhostSimulations.
Require Import Omega.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import TermsAndIndicesFromOneLogInterface.

Require Import AllEntriesIndicesGt0Interface.

Section AllEntriesIndicesGt0.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {taifoli : terms_and_indices_from_one_log_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst_max; rewrite_update; simpl in *
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst_max; rewrite_update; simpl in *
    end.

  Lemma allEntries_indices_gt_0_init :
    refined_raft_net_invariant_init allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_init, allEntries_indices_gt_0.
    simpl. intuition.
  Qed.

  Lemma allEntries_indices_gt_0_client_request :
    refined_raft_net_invariant_client_request allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_client_request, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    find_apply_lem_hyp update_elections_data_client_request_allEntries.
    intuition.
    - find_rewrite. eauto.
    - break_exists. break_and. find_rewrite. simpl in *.
      intuition eauto.
      subst. omega.
  Qed.

  Lemma allEntries_indices_gt_0_timeout :
    refined_raft_net_invariant_timeout allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_timeout, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    find_rewrite_lem update_elections_data_timeout_allEntries.
    eauto.
  Qed.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof.
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma lifted_taifol_nw :
    forall net,
      refined_raft_intermediate_reachable net ->
      forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
        In p (nwPackets net) ->
        pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
        terms_and_indices_from_one entries.
  Proof.
    intros.
    pose proof (lift_prop _ terms_and_indices_from_one_log_nw_invariant).
    match goal with
    | [ H : _ |- _ ] => eapply H; eauto using ghost_packet
    end.
  Qed.

  Lemma allEntries_indices_gt_0_append_entries :
    refined_raft_net_invariant_append_entries allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_append_entries, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    find_apply_lem_hyp update_elections_data_appendEntries_allEntries.
    intuition eauto.
    eapply lifted_taifol_nw; eauto.
  Qed.

  Lemma allEntries_indices_gt_0_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
  Qed.

  Lemma allEntries_indices_gt_0_request_vote :
    refined_raft_net_invariant_request_vote allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_request_vote, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    find_rewrite_lem update_elections_data_requestVote_allEntries.
    eauto.
  Qed.

  Lemma allEntries_indices_gt_0_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    find_rewrite_lem update_elections_data_requestVoteReply_allEntries.
    eauto.
  Qed.

  Lemma allEntries_indices_gt_0_do_leader :
    refined_raft_net_invariant_do_leader allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_do_leader, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    match goal with
    | [ H : nwState ?net ?h = (?x, _) |- _ ] =>
      replace (x) with (fst (nwState net h)) in * by (rewrite H; auto)
    end.
    eauto.
  Qed.

  Lemma allEntries_indices_gt_0_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, allEntries_indices_gt_0.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    match goal with
    | [ H : nwState ?net ?h = (?x, _) |- _ ] =>
      replace (x) with (fst (nwState net h)) in * by (rewrite H; auto)
    end.
    eauto.
  Qed.

  Lemma allEntries_indices_gt_0_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, allEntries_indices_gt_0.
    intros.
    repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma allEntries_indices_gt_0_reboot :
    refined_raft_net_invariant_reboot allEntries_indices_gt_0.
  Proof.
    unfold refined_raft_net_invariant_reboot, allEntries_indices_gt_0.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct; eauto.
    match goal with
    | [ H : nwState ?net ?h = (?x, _) |- _ ] =>
      replace (x) with (fst (nwState net h)) in * by (rewrite H; auto)
    end.
    eauto.
  Qed.

  Lemma allEntries_indices_gt_0_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      allEntries_indices_gt_0 net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply allEntries_indices_gt_0_init.
    - apply allEntries_indices_gt_0_client_request.
    - apply allEntries_indices_gt_0_timeout.
    - apply allEntries_indices_gt_0_append_entries.
    - apply allEntries_indices_gt_0_append_entries_reply.
    - apply allEntries_indices_gt_0_request_vote.
    - apply allEntries_indices_gt_0_request_vote_reply.
    - apply allEntries_indices_gt_0_do_leader.
    - apply allEntries_indices_gt_0_do_generic_server.
    - apply allEntries_indices_gt_0_state_same_packet_subset.
    - apply allEntries_indices_gt_0_reboot.
  Qed.

  Instance aeigt0 : allEntries_indices_gt_0_interface.
  Proof.
    constructor.
    exact allEntries_indices_gt_0_invariant.
  Qed.
End AllEntriesIndicesGt0.
