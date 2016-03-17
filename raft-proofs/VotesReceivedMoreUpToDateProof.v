Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import CommonTheorems.

Require Import RequestVoteReplyMoreUpToDateInterface.

Require Import VotesReceivedMoreUpToDateInterface.

Section VotesReceivedMoreUpToDate.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {rvrmutdi : requestVoteReply_moreUpToDate_interface}.

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
  
  
  Lemma votesReceived_moreUpToDate_append_entries :
    refined_raft_net_invariant_append_entries votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_append_entries; eauto;
    find_copy_apply_lem_hyp handleAppendEntries_votesReceived;
    find_apply_lem_hyp handleAppendEntries_log_term_type;
    intuition; repeat find_rewrite; try congruence;
    eauto;
    rewrite votesWithLog_same_append_entries;
    eauto.
  Qed.

  Lemma votesReceived_moreUpToDate_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    find_copy_apply_lem_hyp handleAppendEntriesReply_votesReceived.
    find_copy_apply_lem_hyp handleAppendEntriesReply_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    intuition; try congruence; repeat find_rewrite; eauto.
  Qed.
  
  Lemma votesReceived_moreUpToDate_request_vote :
    refined_raft_net_invariant_request_vote votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    find_copy_apply_lem_hyp handleRequestVote_votesReceived.
    find_copy_apply_lem_hyp handleRequestVote_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    intuition; try congruence; repeat find_rewrite; eauto;
    copy_eapply_prop_hyp In In; eauto;
    rewrite <- plus_n_O in *;
    break_exists_exists; intuition;
    eauto using update_elections_data_request_vote_votesWithLog_old.
  Qed.

  Lemma votesReceived_moreUpToDate_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - erewrite handleRequestVoteReply_log; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
      intuition.
      repeat find_rewrite.
      find_apply_lem_hyp handleRequestVoteReply_votesReceived.
      rewrite update_elections_data_request_vote_reply_votesWithLog.
      intuition; eauto.
      repeat find_rewrite. subst.
      find_eapply_lem_hyp requestVoteReply_moreUpToDate_invariant; eauto.
    - erewrite handleRequestVoteReply_log; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
      intuition.
      repeat find_rewrite.
      find_apply_lem_hyp handleRequestVoteReply_votesReceived.
      intuition; eauto.
      repeat find_rewrite. subst.
      find_eapply_lem_hyp requestVoteReply_moreUpToDate_invariant; eauto.
    - rewrite update_elections_data_request_vote_reply_votesWithLog.
      eauto.
  Qed.

  Lemma votesReceived_moreUpToDate_timeout :
    refined_raft_net_invariant_timeout votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
      intuition; try congruence.
      repeat find_rewrite. simpl in *. intuition. subst.
      exists (log d). intuition. auto using moreUpToDate_refl.
    - find_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
      intuition; try congruence.
      repeat find_rewrite. simpl in *. intuition.
    - eapply_prop_hyp Candidate Candidate; eauto.
      break_exists_exists. intuition.
      apply update_elections_data_timeout_votesWithLog_old.
      rewrite <- plus_n_O in *. auto.
  Qed.

  Lemma votesReceived_moreUpToDate_client_request :
    refined_raft_net_invariant_client_request votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_client_request; 
    try solve [ find_apply_lem_hyp handleClientRequest_candidate; subst; eauto];
    eauto.
  Qed.

  Lemma votesReceived_moreUpToDate_do_leader :
    refined_raft_net_invariant_do_leader votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_apply_lem_hyp doLeader_candidate; subst; eauto.
  Qed.
  
  Lemma votesReceived_moreUpToDate_do_generic_server :
    refined_raft_net_invariant_do_generic_server votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_apply_lem_hyp doGenericServer_log_type_term_votesReceived;
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma votesReceived_moreUpToDate_reboot :
    refined_raft_net_invariant_reboot votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; congruence.
  Qed.

  Lemma votesReceived_moreUpToDate_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    subst. repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma votesReceived_moreUpToDate_init :
    refined_raft_net_invariant_init votesReceived_moreUpToDate.
  Proof.
    red. unfold votesReceived_moreUpToDate. intros. simpl in *.
    intuition.
  Qed.
  
  Instance vrmutdi : votesReceived_moreUpToDate_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply votesReceived_moreUpToDate_init.
  - apply votesReceived_moreUpToDate_client_request.
  - apply votesReceived_moreUpToDate_timeout.
  - apply votesReceived_moreUpToDate_append_entries.
  - apply votesReceived_moreUpToDate_append_entries_reply.
  - apply votesReceived_moreUpToDate_request_vote.
  - apply votesReceived_moreUpToDate_request_vote_reply.
  - apply votesReceived_moreUpToDate_do_leader.
  - apply votesReceived_moreUpToDate_do_generic_server.
  - apply votesReceived_moreUpToDate_state_same_packet_subset.
  - apply votesReceived_moreUpToDate_reboot.
  Qed.
  
End VotesReceivedMoreUpToDate.
