Require Import Raft.
Require Import RaftRefinementInterface.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import CommonTheorems.

Require Import RequestVoteMaxIndexMaxTermInterface.
Require Import VotedForTermSanityInterface.

Require Import VotedForMoreUpToDateInterface.

Section VotedForMoreUpToDate.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {rvmimti : requestVote_maxIndex_maxTerm_interface}.
  Context {vftsi : votedFor_term_sanity_interface}.

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
  
  
  Lemma votedFor_moreUpToDate_append_entries :
    refined_raft_net_invariant_append_entries votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_append_entries; eauto.
    - find_copy_eapply_lem_hyp handleAppendEntries_term_votedFor; eauto.
      find_apply_lem_hyp handleAppendEntries_log_term_type.
      intuition; try congruence. repeat find_rewrite. eauto.
    - find_copy_eapply_lem_hyp handleAppendEntries_term_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
    - find_apply_lem_hyp handleAppendEntries_log_term_type.
      intuition; try congruence. repeat find_rewrite. eauto.
  Qed.

  Lemma votedFor_moreUpToDate_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    find_copy_apply_lem_hyp handleAppendEntriesReply_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    intuition; try congruence; repeat find_rewrite; eauto;
    find_copy_eapply_lem_hyp handleAppendEntriesReply_term_votedFor; eauto;
    intuition; repeat find_rewrite; eauto.
  Qed.
  
  Lemma votedFor_moreUpToDate_request_vote :
    refined_raft_net_invariant_request_vote votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    find_copy_apply_lem_hyp handleRequestVote_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    intuition; try congruence; repeat find_rewrite; eauto.
    - find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto.
      intuition; repeat find_rewrite.
      + eapply_prop_hyp RaftState.votedFor RaftState.votedFor; eauto.
        break_exists_exists; intuition.
        eauto using update_elections_data_request_vote_votesWithLog_old.
      + simpl. eauto using moreUpToDate_refl.
    - find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto.
      intuition; repeat find_rewrite.
      + eapply_prop_hyp RaftState.votedFor RaftState.votedFor; eauto.
        break_exists_exists; intuition.
        eauto using update_elections_data_request_vote_votesWithLog_old.
      + find_apply_lem_hyp requestVote_maxIndex_maxTerm_invariant.
        subst.
        eapply_prop_hyp requestVote_maxIndex_maxTerm pBody. conclude_using eauto.
        all:eauto.
        intuition; subst.
        eexists; intuition; eauto.
    - find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto.
      intuition; repeat find_rewrite.
      + eapply_prop_hyp RaftState.votedFor RaftState.votedFor; eauto.
        break_exists_exists; intuition.
        eauto using update_elections_data_request_vote_votesWithLog_old.
      + find_apply_lem_hyp requestVote_maxIndex_maxTerm_invariant.
        subst.
        eapply_prop_hyp requestVote_maxIndex_maxTerm pBody. conclude_using eauto.
        all:eauto.
        intuition; subst.
        eexists; intuition; eauto.
  Qed.

  Lemma votedFor_moreUpToDate_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *;
    try rewrite update_elections_data_request_vote_reply_votesWithLog;
    eauto.
    - erewrite handleRequestVoteReply_log; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_term_votedFor; eauto.
      intuition. repeat find_rewrite. eauto.
    - find_copy_eapply_lem_hyp handleRequestVoteReply_term_votedFor; eauto.
      intuition. repeat find_rewrite. eauto.
    - erewrite handleRequestVoteReply_log; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
      intuition. repeat find_rewrite. eauto.
  Qed.
  
  Lemma votedFor_moreUpToDate_timeout :
    refined_raft_net_invariant_timeout votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_apply_lem_hyp handleTimeout_log_same.
      find_copy_eapply_lem_hyp update_elections_data_timeout_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
      simpl. eauto using moreUpToDate_refl.
    - find_copy_eapply_lem_hyp update_elections_data_timeout_votedFor; eauto.
      intuition; [repeat find_rewrite; eauto|].
      subst. omega.
    - find_copy_apply_lem_hyp handleTimeout_log_same.
      find_apply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived.
      intuition; try congruence.
      find_copy_apply_lem_hyp votedFor_term_sanity_invariant.
      eapply_prop_hyp votedFor_term_sanity RaftState.votedFor; eauto.
      unfold raft_data in *; simpl in *; unfold raft_data in *; simpl in *.
      omega.
  Qed.

  Lemma votedFor_moreUpToDate_client_request :
    refined_raft_net_invariant_client_request votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleClientRequest_type; intuition.
    find_copy_apply_lem_hyp handleClientRequest_term_votedFor; intuition.
    destruct_update; simpl in *; eauto; repeat find_rewrite;
    try rewrite votesWithLog_same_client_request;
    find_apply_lem_hyp handleClientRequest_log;
    intuition; repeat find_rewrite; eauto;
    break_exists; intuition; congruence.
  Qed.

  Lemma votedFor_moreUpToDate_do_leader :
    refined_raft_net_invariant_do_leader votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try solve [find_apply_lem_hyp doLeader_candidate; subst; eauto].
    find_apply_lem_hyp doLeader_term_votedFor.
    intuition; repeat find_rewrite; eauto.
  Qed.
  
  Lemma votedFor_moreUpToDate_do_generic_server :
    refined_raft_net_invariant_do_generic_server votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
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

  Lemma votedFor_moreUpToDate_reboot :
    refined_raft_net_invariant_reboot votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; congruence.
  Qed.

  Lemma votedFor_moreUpToDate_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    subst. repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma votedFor_moreUpToDate_init :
    refined_raft_net_invariant_init votedFor_moreUpToDate.
  Proof.
    red. unfold votedFor_moreUpToDate. intros. simpl in *.
    congruence.
  Qed.
  
  Instance vfmutdi : votedFor_moreUpToDate_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply votedFor_moreUpToDate_init.
  - apply votedFor_moreUpToDate_client_request.
  - apply votedFor_moreUpToDate_timeout.
  - apply votedFor_moreUpToDate_append_entries.
  - apply votedFor_moreUpToDate_append_entries_reply.
  - apply votedFor_moreUpToDate_request_vote.
  - apply votedFor_moreUpToDate_request_vote_reply.
  - apply votedFor_moreUpToDate_do_leader.
  - apply votedFor_moreUpToDate_do_generic_server.
  - apply votedFor_moreUpToDate_state_same_packet_subset.
  - apply votedFor_moreUpToDate_reboot.
  Qed.
  
End VotedForMoreUpToDate.
