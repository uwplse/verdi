Require Import Raft.
Require Import RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import SpecLemmas.

Require Import RequestVoteTermSanityInterface.

Section RequestVoteTermSanity.
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


  
  Lemma requestVote_term_sanity_append_entries :
    refined_raft_net_invariant_append_entries requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    assert (In p0 (nwPackets net)) by
        (find_apply_hyp_hyp; repeat find_rewrite; intuition; [in_crush|];
         exfalso; subst; simpl in *; subst;
         unfold handleAppendEntries in *;
           repeat break_match; find_inversion).
    repeat find_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleAppendEntries_currentTerm_leaderId.
    intuition; repeat find_rewrite; eauto;
    eapply_prop_hyp pBody pBody; eauto; omega.
  Qed.

  Lemma requestVote_term_sanity_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    assert (In p0 (nwPackets net)) by
        (repeat find_rewrite;
         find_apply_lem_hyp handleAppendEntriesReply_packets;
         subst; simpl in *; find_apply_hyp_hyp; intuition; in_crush).
    repeat find_rewrite.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    repeat find_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_type_term;
      intuition; eauto;
      eapply_prop_hyp pBody pBody; eauto; omega.
  Qed.
  
  Lemma requestVote_term_sanity_request_vote :
    refined_raft_net_invariant_request_vote requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *. subst.
    assert (In p0 (nwPackets net)) by
        (repeat find_rewrite; find_apply_hyp_hyp; intuition; try solve [in_crush];
         exfalso; subst; simpl in *; subst;
         unfold handleRequestVote in *;
           repeat break_match; find_inversion; congruence).
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
    intuition; repeat find_rewrite; eauto;
    eapply_prop_hyp pBody pBody; eauto; omega.
  Qed.
  
  Lemma requestVote_term_sanity_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_apply_hyp_hyp.
    assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
    repeat find_rewrite.
    eauto using handleRequestVoteReply_currentTerm.
  Qed.

  Lemma requestVote_term_sanity_timeout :
    refined_raft_net_invariant_timeout requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_apply_hyp_hyp. intuition.
      + find_apply_lem_hyp handleTimeout_log_term_type.
        intuition; repeat find_rewrite; eauto.
      + do_in_map. remember (pSrc p). subst p. simpl in *.
        find_eapply_lem_hyp handleTimeout_messages; eauto; intuition.
    - find_apply_hyp_hyp. intuition.
      + find_apply_lem_hyp handleTimeout_log_term_type.
        intuition; repeat find_rewrite; eauto.
      + do_in_map. remember (pSrc p). subst p. simpl in *.
        congruence.
  Qed.
  
  Lemma requestVote_term_sanity_client_request :
    refined_raft_net_invariant_client_request requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    find_copy_apply_lem_hyp handleClientRequest_packets.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_apply_lem_hyp handleClientRequest_term_votedFor.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma requestVote_term_sanity_do_leader :
    refined_raft_net_invariant_do_leader requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    assert (In p (nwPackets net)) by
        (find_apply_hyp_hyp; intuition;
         do_in_map; subst;
         unfold doLeader, replicaMessage in *;
           repeat break_match; find_inversion; subst; simpl in *; intuition;
         do_in_map; subst; simpl in *; congruence).
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_apply_lem_hyp doLeader_term_votedFor; intuition; repeat find_rewrite; eauto.
  Qed.
  
  Lemma requestVote_term_sanity_do_generic_server :
    refined_raft_net_invariant_do_generic_server requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    find_copy_apply_lem_hyp doGenericServer_packets. subst. simpl in *.
    find_apply_hyp_hyp. intuition.
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

  Lemma requestVote_term_sanity_reboot :
    refined_raft_net_invariant_reboot requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; congruence.
  Qed.

  Lemma requestVote_term_sanity_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    subst. repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma requestVote_term_sanity_init :
    refined_raft_net_invariant_init requestVote_term_sanity.
  Proof.
    red. unfold requestVote_term_sanity. intros. simpl in *.
    intuition.
  Qed.
  
  Instance rvtsi : requestVote_term_sanity_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply requestVote_term_sanity_init.
  - apply requestVote_term_sanity_client_request.
  - apply requestVote_term_sanity_timeout.
  - apply requestVote_term_sanity_append_entries.
  - apply requestVote_term_sanity_append_entries_reply.
  - apply requestVote_term_sanity_request_vote.
  - apply requestVote_term_sanity_request_vote_reply.
  - apply requestVote_term_sanity_do_leader.
  - apply requestVote_term_sanity_do_generic_server.
  - apply requestVote_term_sanity_state_same_packet_subset.
  - apply requestVote_term_sanity_reboot.
  Qed.
  
  
End RequestVoteTermSanity.
