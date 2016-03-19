Require Import Raft.
Require Import RaftRefinementInterface.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AllEntriesTermSanityInterface.

Section AllEntriesTermSanity.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri: raft_refinement_interface}.


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

  Lemma allEntries_term_sanity_append_entries :
    refined_raft_net_invariant_append_entries allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_eapply_lem_hyp update_elections_data_appendEntries_allEntries_term'; eauto.
    intuition.
    find_apply_lem_hyp handleAppendEntries_currentTerm_monotonic;
      find_apply_hyp_hyp; omega.
  Qed.

  Lemma allEntries_term_sanity_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_apply_lem_hyp handleAppendEntriesReply_type_term. intuition; repeat find_rewrite; eauto.
    find_apply_hyp_hyp. omega.
  Qed.

  Lemma allEntries_term_sanity_request_vote :
    refined_raft_net_invariant_request_vote allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_rewrite_lem update_elections_data_requestVote_allEntries.
    find_apply_lem_hyp handleRequestVote_type_term. intuition; repeat find_rewrite; eauto.
    find_apply_hyp_hyp. omega.
  Qed.

  Lemma allEntries_term_sanity_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_rewrite_lem update_elections_data_requestVoteReply_allEntries.
    find_apply_hyp_hyp.
    unfold handleRequestVoteReply, advanceCurrentTerm.
    repeat break_match; simpl in *; repeat find_inversion; do_bool; simpl in *; auto.
    omega.
  Qed.

  Lemma allEntries_term_sanity_client_request :
    refined_raft_net_invariant_client_request allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp update_elections_data_client_request_allEntries.
    find_apply_lem_hyp handleClientRequest_type.
    intuition; repeat find_rewrite;
    try find_apply_hyp_hyp; auto.
    break_exists.
    intuition; repeat find_rewrite;
    simpl in *.
    intuition; simpl in *;
    try match goal with
      | H : context [ _ :: _ ] |- _ => clear H
    end; repeat tuple_inversion; eauto.
  Qed.

  Lemma allEntries_term_sanity_timeout :
    refined_raft_net_invariant_timeout allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_rewrite_lem update_elections_data_timeout_allEntries.
    find_apply_lem_hyp handleTimeout_type_strong.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma allEntries_term_sanity_do_leader :
    refined_raft_net_invariant_do_leader allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_apply_lem_hyp doLeader_type. intuition.
    repeat find_rewrite. eauto.
  Qed.
    

  Lemma allEntries_term_sanity_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_apply_lem_hyp doGenericServer_type. intuition.
    repeat find_rewrite. eauto.
  Qed.
  

  Lemma allEntries_term_sanity_reboot :
    refined_raft_net_invariant_reboot allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.
      

  Lemma allEntries_term_sanity_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros.
    find_reverse_higher_order_rewrite. eauto.
  Qed.


  Lemma allEntries_term_sanity_init :
    refined_raft_net_invariant_init allEntries_term_sanity.
  Proof.
    red. unfold allEntries_term_sanity. intros. simpl in *. intuition.
  Qed.
  
  Instance aetsi : allEntries_term_sanity_interface.
  Proof.
    split.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply allEntries_term_sanity_init.
    - apply allEntries_term_sanity_client_request.
    - apply allEntries_term_sanity_timeout.
    - apply allEntries_term_sanity_append_entries.
    - apply allEntries_term_sanity_append_entries_reply.
    - apply allEntries_term_sanity_request_vote.
    - apply allEntries_term_sanity_request_vote_reply.
    - apply allEntries_term_sanity_do_leader.
    - apply allEntries_term_sanity_do_generic_server.
    - apply allEntries_term_sanity_state_same_packet_subset.
    - apply allEntries_term_sanity_reboot.
  Qed. 
End AllEntriesTermSanity.
