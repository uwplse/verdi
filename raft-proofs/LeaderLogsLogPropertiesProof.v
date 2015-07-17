Require Import List.
Import ListNotations.

Require Import Util.
Require Import Net.

Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import VerdiTactics.
Require Import Raft.
Require Import VerdiTactics.
Require Import RaftRefinementInterface.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import SpecLemmas.

Require Import LeaderLogsLogPropertiesInterface.
Require Import RefinementSpecLemmas.

Section LeaderLogsLogProperties.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rri : raft_refinement_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).

  (*
  Example contiguous_log_property :
    log_property (fun l => contiguous_range_exact_lo l 0).
  Proof.
    red. intros.
    apply entries_contiguous_invariant; auto.
  Qed.
   *)
    

  Lemma log_properties_hold_on_leader_logs_init :
    refined_raft_net_invariant_init log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs.
    intros. simpl in *. intuition.
  Qed.

  Ltac finish := solve [eapply_prop_hyp In In; eauto].
    
  Lemma log_properties_hold_on_leader_logs_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; [|finish].
    find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
    intuition; [finish|].
    subst.
    erewrite handleRequestVoteReply_log; eauto.
  Qed.

  Lemma log_properties_hold_on_leader_logs_append_entries :
    refined_raft_net_invariant_append_entries log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; [|finish].
    find_erewrite_lem update_elections_data_appendEntries_leaderLogs; eauto.
    finish.
  Qed.

  Lemma log_properties_hold_on_leader_logs_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; finish.
  Qed.
  
  Lemma log_properties_hold_on_leader_logs_request_vote :
    refined_raft_net_invariant_request_vote log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; [|finish].
    find_erewrite_lem leaderLogs_update_elections_data_requestVote; eauto.
    finish.
  Qed.

  Lemma log_properties_hold_on_leader_logs_do_leader :
    refined_raft_net_invariant_do_leader log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; finish.
  Qed.


  Lemma log_properties_hold_on_leader_logs_do_generic_server :
    refined_raft_net_invariant_do_generic_server log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; finish.
  Qed.

  Lemma log_properties_hold_on_leader_logs_reboot :
    refined_raft_net_invariant_reboot log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; finish.
  Qed.

  Lemma log_properties_hold_on_leader_logs_client_request :
    refined_raft_net_invariant_client_request log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; [|finish].
    find_erewrite_lem update_elections_data_client_request_leaderLogs; eauto.
    finish.
  Qed.


  Lemma log_properties_hold_on_leader_logs_timeout :
    refined_raft_net_invariant_timeout log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; [|finish].
    find_erewrite_lem update_elections_data_timeout_leaderLogs; eauto.
    finish.
  Qed.


  Lemma log_properties_hold_on_leader_logs_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset log_properties_hold_on_leader_logs.
  Proof.
    red. unfold log_properties_hold_on_leader_logs. intros.
    simpl in *.
    subst. repeat find_reverse_higher_order_rewrite. finish.
  Qed.
  
  
  Theorem log_properties_hold_on_leader_logs_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      log_properties_hold_on_leader_logs net.
  Proof.
    intros. apply refined_raft_net_invariant; auto.
    - apply log_properties_hold_on_leader_logs_init.
    - apply log_properties_hold_on_leader_logs_client_request.
    - apply log_properties_hold_on_leader_logs_timeout.
    - apply log_properties_hold_on_leader_logs_append_entries.
    - apply log_properties_hold_on_leader_logs_append_entries_reply.
    - apply log_properties_hold_on_leader_logs_request_vote.
    - apply log_properties_hold_on_leader_logs_request_vote_reply.
    - apply log_properties_hold_on_leader_logs_do_leader.
    - apply log_properties_hold_on_leader_logs_do_generic_server.
    - apply log_properties_hold_on_leader_logs_state_same_packet_subset.
    - apply log_properties_hold_on_leader_logs_reboot.
  Qed.

  Instance lpholli : log_properties_hold_on_leader_logs_interface.
  split.
  auto using log_properties_hold_on_leader_logs_invariant.
  Defined.
  
End LeaderLogsLogProperties.
