Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import CommonTheorems.

Require Import RequestVoteTermSanityInterface.
Require Import VotedForTermSanityInterface.

Section VotedForTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {rvtsi : requestVote_term_sanity_interface}.
  
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

  Lemma votedFor_term_sanity_append_entries :
    refined_raft_net_invariant_append_entries votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. simpl in *.
    intros. subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_eapply_lem_hyp handleAppendEntries_term_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
    - find_copy_apply_lem_hyp handleAppendEntries_currentTerm_leaderId.
      intuition; eauto;
      eapply_prop_hyp RaftState.votedFor RaftState.votedFor; eauto;
      try rewrite <- plus_n_O in *; omega.
  Qed.


  Lemma votedFor_term_sanity_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. simpl in *.
    intros. subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_eapply_lem_hyp handleAppendEntriesReply_term_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
    - find_copy_apply_lem_hyp handleAppendEntriesReply_type_term;
      intuition; eauto;
      eapply_prop_hyp RaftState.votedFor RaftState.votedFor; eauto;
      try rewrite <- plus_n_O in *; omega.
  Qed.

  Lemma votedFor_term_sanity_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. simpl in *.
    intros. subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_eapply_lem_hyp handleRequestVoteReply_term_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
    - eauto using handleRequestVoteReply_currentTerm.
  Qed.

  Lemma votedFor_term_sanity_request_vote :
    refined_raft_net_invariant_request_vote votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. simpl in *.
    intros. subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
      eapply requestVote_term_sanity_invariant; eauto.
    - find_copy_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
      intuition; repeat find_rewrite; eauto;
      eapply_prop_hyp RaftState.votedFor RaftState.votedFor; eauto;
      try rewrite <- plus_n_O in *; omega.
  Qed.

  Lemma votedFor_term_sanity_timeout :
    refined_raft_net_invariant_timeout votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. simpl in *.
    intros. subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_eapply_lem_hyp update_elections_data_timeout_votedFor; eauto.
      intuition; repeat find_rewrite; eauto.
      congruence.
    - find_copy_apply_lem_hyp handleTimeout_type_strong.
      intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma votedFor_term_sanity_client_request :
    refined_raft_net_invariant_client_request votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. simpl in *.
    intros. subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_copy_eapply_lem_hyp handleClientRequest_term_votedFor;
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma votedFor_term_sanity_do_leader :
    refined_raft_net_invariant_do_leader votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_copy_eapply_lem_hyp doLeader_term_votedFor;
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma votedFor_term_sanity_do_generic_server :
    refined_raft_net_invariant_do_generic_server votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_copy_eapply_lem_hyp doGenericServer_log_type_term_votesReceived;
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma votedFor_term_sanity_reboot :
    refined_raft_net_invariant_reboot votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.

  Lemma votedFor_term_sanity_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. intros. simpl in *.
    repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma votedFor_term_sanity_init :
    refined_raft_net_invariant_init votedFor_term_sanity.
  Proof.
    red. unfold votedFor_term_sanity in *. intros. simpl in *. congruence.
  Qed.
  
  Instance vftsi : votedFor_term_sanity_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply votedFor_term_sanity_init.
  - apply votedFor_term_sanity_client_request.
  - apply votedFor_term_sanity_timeout.
  - apply votedFor_term_sanity_append_entries.
  - apply votedFor_term_sanity_append_entries_reply.
  - apply votedFor_term_sanity_request_vote.
  - apply votedFor_term_sanity_request_vote_reply.
  - apply votedFor_term_sanity_do_leader.
  - apply votedFor_term_sanity_do_generic_server.
  - apply votedFor_term_sanity_state_same_packet_subset.
  - apply votedFor_term_sanity_reboot.
  Qed.

End VotedForTermSanity.
