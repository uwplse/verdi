Require Import List.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.
Require Import RefinementCommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import TermSanityInterface.
Require Import LogAllEntriesInterface.

Section LogAllEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {tsi : term_sanity_interface}.

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

  Ltac rewrite_goal :=
    match goal with
      | H: _ = _ |- _ => rewrite H
    end.
    
  Definition no_entries_past_current_term_host_lifted net :=
    forall (h : name) e,
      In e (log (snd (nwState net h))) ->
      eTerm e <= currentTerm (snd (nwState net h)).

  Lemma no_entries_past_current_term_host_lifted_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      no_entries_past_current_term_host_lifted net.
  Proof.
    unfold no_entries_past_current_term_host_lifted.
    pose proof deghost_spec.
    do 4 intro.
    repeat find_reverse_higher_order_rewrite.
    eapply lift_prop; eauto.
    intros.
    find_apply_lem_hyp no_entries_past_current_term_invariant; eauto.
  Qed.

  Lemma handleAppendEntries_currentTerm_monotonic:
    forall h st (d : raft_data) 
      (m : msg) (t : term) (n : name) (pli : logIndex) 
      (plt : term) (es : list entry) (ci : logIndex),
      handleAppendEntries h st t n pli plt es
                          ci = (d, m) ->
      currentTerm st <= currentTerm d.
  Proof.
    intros.
    unfold handleAppendEntries in *.
    repeat break_match; simpl in *; do_bool; repeat find_inversion; auto; try omega;
    simpl in *;
    unfold advanceCurrentTerm in *; repeat break_match; do_bool; auto.
  Qed.
  
  Lemma log_all_entries_append_entries :
    refined_raft_net_invariant_append_entries log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp handleAppendEntries_currentTerm_monotonic.
    find_eapply_lem_hyp update_elections_data_appendEntries_log_allEntries;
      intuition; eauto; repeat find_rewrite; repeat rewrite_goal; eauto.
    - copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
      find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
      repeat find_rewrite. eauto using le_antisym.
    - subst.
      apply in_app_iff. right.
      find_apply_hyp_hyp.
      find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
      eauto using le_antisym.
    - subst.
      apply in_app_iff.
      left.
      apply in_map_iff. eauto.
    - do_in_app. intuition.
      + subst.
        apply in_app_iff.
        left.
        apply in_map_iff. eauto.
      + subst.
        apply in_app_iff. right.
        find_apply_lem_hyp removeAfterIndex_in.
        find_apply_hyp_hyp.
        find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
        eauto using le_antisym.
  Qed.

  Lemma log_all_entries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp handleAppendEntriesReply_log. find_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_type_term.
    intuition; repeat find_rewrite; copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
    find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
    repeat find_rewrite. eauto using le_antisym.
  Qed.

  Lemma log_all_entries_request_vote :
    refined_raft_net_invariant_request_vote log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp handleRequestVote_log. find_rewrite.
    find_copy_apply_lem_hyp handleRequestVote_type_term.
    rewrite update_elections_data_requestVote_allEntries.
    intuition; repeat find_rewrite; copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
    find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
    repeat find_rewrite. eauto using le_antisym.
  Qed.


  Lemma log_all_entries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_erewrite_lem handleRequestVoteReply_log.
    rewrite update_elections_data_requestVoteReply_allEntries.
    match goal with
      | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?v] =>
        pose proof handleRequestVoteReply_type h st h' t v
             (handleRequestVoteReply h st h' t v)
    end.
    intuition; repeat find_rewrite;
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
    find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
    repeat find_rewrite.
    unfold raft_data in *. simpl in *. 
    unfold raft_data in *. simpl in *.
    omega.
  Qed.

  Lemma log_all_entries_do_leader :
    refined_raft_net_invariant_do_leader log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp doLeader_type; intuition.
    find_apply_lem_hyp doLeader_log. repeat find_rewrite.
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
  Qed.
  

  Lemma log_all_entries_do_generic_server :
    refined_raft_net_invariant_do_generic_server log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp doGenericServer_type; intuition.
    find_apply_lem_hyp doGenericServer_log. repeat find_rewrite.
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
  Qed.

  Lemma log_all_entries_client_request :
    refined_raft_net_invariant_client_request log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp update_elections_data_client_request_log_allEntries.
    find_apply_lem_hyp handleClientRequest_type.
    intuition; repeat find_rewrite;
    [copy_eapply_prop_hyp In In; repeat find_rewrite; auto|].
    break_exists. intuition.
    repeat find_rewrite.  simpl in *. intuition; subst; auto.
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
  Qed.

  Lemma log_all_entries_timeout :
    refined_raft_net_invariant_timeout log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|copy_eapply_prop_hyp In In; repeat find_rewrite; auto].
    find_copy_apply_lem_hyp handleTimeout_log_same.
    rewrite update_elections_data_timeout_allEntries.
    find_apply_lem_hyp handleTimeout_type_strong.
    intuition; repeat find_rewrite;
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
    find_apply_lem_hyp no_entries_past_current_term_host_lifted_invariant; auto.
    repeat find_rewrite.
    unfold raft_data in *. simpl in *. 
    unfold raft_data in *. simpl in *.
    omega.
  Qed.

  Lemma log_all_entries_reboot :
    refined_raft_net_invariant_reboot log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
  Qed.

  Lemma log_all_entries_init :
    refined_raft_net_invariant_init log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *. intuition.
  Qed.

  Lemma log_all_entries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset log_all_entries.
  Proof.
    red. unfold log_all_entries. intros.
    simpl in *.
    repeat find_reverse_higher_order_rewrite.
    copy_eapply_prop_hyp In In; repeat find_rewrite; auto.
  Qed.

  Theorem log_all_entries_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      log_all_entries net.
  Proof.
    intros. apply refined_raft_net_invariant; auto.
    - apply log_all_entries_init.
    - apply log_all_entries_client_request.
    - apply log_all_entries_timeout.
    - apply log_all_entries_append_entries.
    - apply log_all_entries_append_entries_reply.
    - apply log_all_entries_request_vote.
    - apply log_all_entries_request_vote_reply.
    - apply log_all_entries_do_leader.
    - apply log_all_entries_do_generic_server.
    - apply log_all_entries_state_same_packet_subset.
    - apply log_all_entries_reboot.
  Qed.
  
  Instance laei : log_all_entries_interface.
  split.
  auto using log_all_entries_invariant.
  Qed.
End LogAllEntries.
