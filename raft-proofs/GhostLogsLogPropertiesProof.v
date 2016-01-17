Require Import List.
Import ListNotations.

Require Import Util.
Require Import Net.
Require Import GhostSimulations.

Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import VerdiTactics.
Require Import Raft.
Require Import VerdiTactics.
Require Import RaftMsgRefinementInterface.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import SpecLemmas.

Require Import GhostLogsLogPropertiesInterface.

Section GhostLogsLogProperties.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rmri : raft_msg_refinement_interface}.

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

  Lemma log_properties_hold_on_ghost_logs_init :
    msg_refined_raft_net_invariant_init log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs.
    intros. simpl in *. intuition.
  Qed.
    
  Lemma log_properties_hold_on_ghost_logs_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
  Qed.

  Lemma log_properties_hold_on_ghost_logs_append_entries :
    msg_refined_raft_net_invariant_append_entries' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} (pDst p)))
      by (simpl; repeat find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.

  Lemma log_properties_hold_on_ghost_logs_request_vote :
    msg_refined_raft_net_invariant_request_vote' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} (pDst p))) by
        (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.

  Lemma log_properties_hold_on_ghost_logs_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    do_in_map. subst.
    simpl in *.
    unfold add_ghost_msg, write_ghost_msg in *.
    do_in_map. 
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} (pDst p))) by
        (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.


  Lemma log_properties_hold_on_ghost_logs_client_request :
    msg_refined_raft_net_invariant_client_request' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    do_in_map. subst.
    simpl in *.
    unfold add_ghost_msg, write_ghost_msg in *.
    do_in_map. 
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} h)) by
        (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.

  Lemma log_properties_hold_on_ghost_logs_timeout :
    msg_refined_raft_net_invariant_timeout' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    do_in_map. subst.
    simpl in *.
    unfold add_ghost_msg, write_ghost_msg in *.
    do_in_map. 
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} h)) by
        (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.  

  Lemma log_properties_hold_on_ghost_logs_do_leader :
    msg_refined_raft_net_invariant_do_leader' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    do_in_map. subst.
    simpl in *.
    unfold add_ghost_msg, write_ghost_msg in *.
    do_in_map. 
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d' with (snd (nwState {| nwPackets := ps'; nwState := st' |} h)) by
        (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.  

  Lemma log_properties_hold_on_ghost_logs_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server' log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst.
    find_apply_hyp_hyp; intuition; repeat find_rewrite;
    try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
    do_in_map. subst.
    simpl in *.
    unfold add_ghost_msg, write_ghost_msg in *.
    do_in_map. 
    subst. simpl in *.
    unfold write_ghost_log. simpl in *.
    replace d' with (snd (nwState {| nwPackets := ps'; nwState := st' |} h)) by
        (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
    eauto.
  Qed.  

  Lemma log_properties_hold_on_ghost_logs_reboot :
    msg_refined_raft_net_invariant_reboot log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst. repeat find_reverse_rewrite.
    eapply_prop_hyp msg_log_property msg_log_property; eauto.
  Qed.

  Lemma log_properties_hold_on_ghost_logs_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset log_properties_hold_on_ghost_logs.
  Proof.
    red. unfold log_properties_hold_on_ghost_logs. intros.
    simpl in *.
    subst. repeat find_reverse_rewrite.
    eapply_prop_hyp msg_log_property msg_log_property; eauto.
  Qed.
  
  Theorem log_properties_hold_on_ghost_logs_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      log_properties_hold_on_ghost_logs net.
  Proof.
    intros. apply msg_refined_raft_net_invariant'; auto.
    - apply log_properties_hold_on_ghost_logs_init.
    - apply log_properties_hold_on_ghost_logs_client_request.
    - apply log_properties_hold_on_ghost_logs_timeout.
    - apply log_properties_hold_on_ghost_logs_append_entries.
    - apply log_properties_hold_on_ghost_logs_append_entries_reply.
    - apply log_properties_hold_on_ghost_logs_request_vote.
    - apply msg_refined_raft_net_invariant_request_vote_reply'_weak.
      apply log_properties_hold_on_ghost_logs_request_vote_reply.
    - apply log_properties_hold_on_ghost_logs_do_leader.
    - apply log_properties_hold_on_ghost_logs_do_generic_server.
    - apply msg_refined_raft_net_invariant_subset'_weak.
      apply log_properties_hold_on_ghost_logs_state_same_packet_subset.
    - apply msg_refined_raft_net_invariant_reboot'_weak.
      apply log_properties_hold_on_ghost_logs_reboot.
  Qed.

  Instance lphogli : log_properties_hold_on_ghost_logs_interface.
  split.
  auto using log_properties_hold_on_ghost_logs_invariant.
  Defined.
  
End GhostLogsLogProperties.
