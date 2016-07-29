Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import InLogInAllEntriesInterface.

Section InLogInAllEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).

  Lemma in_log_in_all_entries_append_entries :
    refined_raft_net_invariant_append_entries in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_eapply_lem_hyp update_elections_data_appendEntries_log_allEntries; eauto.
    intuition; repeat find_rewrite; eauto;
    match goal with
      | H : allEntries _ = _ |- _ => rewrite H in *
    end; eauto.
    - copy_eapply_prop_hyp In In.
      break_exists_exists.
      apply in_app_iff.
      eauto.
    - eexists.
      apply in_app_iff.
      left.
      apply in_map_iff.
      eexists; intuition; eauto.
    - do_in_app. intuition.
      + eexists.
        apply in_app_iff.
        left.
        apply in_map_iff.
        eexists; intuition; eauto.
      + find_apply_lem_hyp removeAfterIndex_in.
        copy_eapply_prop_hyp In In.
        break_exists_exists.
        apply in_app_iff.
        eauto.
  Qed.

  Lemma in_log_in_all_entries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_erewrite_lem handleAppendEntriesReply_log. eauto.
  Qed.

  Lemma in_log_in_all_entries_request_vote :
    refined_raft_net_invariant_request_vote in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    rewrite update_elections_data_requestVote_allEntries.
    find_erewrite_lem handleRequestVote_log. eauto.
  Qed.

  Lemma in_log_in_all_entries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    rewrite update_elections_data_requestVoteReply_allEntries.
    find_erewrite_lem handleRequestVoteReply_log. eauto.
  Qed.

  Lemma in_log_in_all_entries_timeout :
    refined_raft_net_invariant_timeout in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    rewrite update_elections_data_timeout_allEntries.
    find_erewrite_lem handleTimeout_log_same. eauto.
  Qed.

  Lemma in_log_in_all_entries_client_request :
    refined_raft_net_invariant_client_request in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_eapply_lem_hyp update_elections_data_client_request_log_allEntries; eauto.
    intuition; try break_exists; intuition; repeat find_rewrite; eauto.
    simpl in *. intuition; subst; eauto.
    copy_eapply_prop_hyp In In. 
    break_exists_exists; eauto.
  Qed.

  Lemma in_log_in_all_entries_do_leader :
    refined_raft_net_invariant_do_leader in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_erewrite_lem doLeader_log; eauto.
  Qed.

  Lemma in_log_in_all_entries_do_generic_server :
    refined_raft_net_invariant_do_generic_server in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_erewrite_lem doGenericServer_log; eauto.
  Qed.

  Lemma in_log_in_all_entries_reboot :
    refined_raft_net_invariant_reboot in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.

  Lemma in_log_in_all_entries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma in_log_in_all_entries_init :
    refined_raft_net_invariant_init in_log_in_all_entries.
  Proof.
    red. unfold in_log_in_all_entries. intros. simpl in *.
    intuition.
  Qed.

  Instance iliaei : in_log_in_all_entries_interface.
  Proof.
    split.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply in_log_in_all_entries_init.
    - apply in_log_in_all_entries_client_request.
    - apply in_log_in_all_entries_timeout.
    - apply in_log_in_all_entries_append_entries.
    - apply in_log_in_all_entries_append_entries_reply.
    - apply in_log_in_all_entries_request_vote.
    - apply in_log_in_all_entries_request_vote_reply.
    - apply in_log_in_all_entries_do_leader.
    - apply in_log_in_all_entries_do_generic_server.
    - apply in_log_in_all_entries_state_same_packet_subset.
    - apply in_log_in_all_entries_reboot.
  Qed. 

End InLogInAllEntries.
