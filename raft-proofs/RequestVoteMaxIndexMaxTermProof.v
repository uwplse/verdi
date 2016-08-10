Require Import Raft.
Require Import RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import RequestVoteMaxIndexMaxTermInterface.
Require Import RequestVoteTermSanityInterface.

Section RequestVoteMaxIndexMaxTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {rvrtsi : requestVote_term_sanity_interface}.

  Lemma requestVote_maxIndex_maxTerm_append_entries :
    refined_raft_net_invariant_append_entries requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    assert (In p0 (nwPackets net)) by
        (find_apply_hyp_hyp; repeat find_rewrite; intuition; [in_crush|];
         exfalso; subst; simpl in *; subst;
         unfold handleAppendEntries in *;
           repeat break_match; find_inversion).
    repeat find_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_append_entries; eauto;
    find_apply_lem_hyp handleAppendEntries_log_term_type.
    break_or_hyp; try congruence.
    break_and; repeat find_rewrite; eauto.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    assert (In p0 (nwPackets net)) by
        (repeat find_rewrite;
         find_apply_lem_hyp handleAppendEntriesReply_packets;
         subst; simpl in *; find_apply_hyp_hyp; intuition; in_crush).
    repeat find_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    break_or_hyp; try congruence; break_and; repeat find_rewrite; eauto.
  Qed.
  
  Lemma requestVote_maxIndex_maxTerm_request_vote :
    refined_raft_net_invariant_request_vote requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    assert (In p0 (nwPackets net)) by
        (find_apply_hyp_hyp; repeat find_rewrite; intuition; [in_crush|];
         exfalso; subst; simpl in *; subst;
         unfold handleRequestVote in *;
           repeat break_match; find_inversion).
    find_copy_apply_lem_hyp handleRequestVote_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    break_or_hyp; try congruence; break_and; repeat find_rewrite; eauto.
  Qed.
  
  Lemma requestVote_maxIndex_maxTerm_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
    break_and; repeat find_rewrite; eauto.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_timeout :
    refined_raft_net_invariant_timeout requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_apply_hyp_hyp. break_or_hyp.
      + exfalso.
        find_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
        intuition; try congruence.
        find_apply_lem_hyp requestVote_term_sanity_invariant.
        eapply_prop_hyp requestVote_term_sanity pBody; eauto.
        unfold raft_data in *; simpl in *; unfold raft_data in *; simpl in *.
        omega.
      + do_in_map. remember (pSrc p). subst p.
        simpl in *.
        intuition; eapply handleTimeout_messages; eauto.
    - find_apply_hyp_hyp. break_or_hyp; eauto.
      do_in_map. subst. simpl in *. intuition.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_client_request :
    refined_raft_net_invariant_client_request requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    find_copy_apply_lem_hyp handleClientRequest_packets.
    subst. simpl in *.
    find_apply_hyp_hyp. break_or_hyp.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_client_request; eauto;
    find_apply_lem_hyp handleClientRequest_candidate; subst; eauto.
    intuition.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_do_leader :
    refined_raft_net_invariant_do_leader requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
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
    find_apply_lem_hyp doLeader_candidate; subst; eauto.
  Qed.
  
  Lemma requestVote_maxIndex_maxTerm_do_generic_server :
    refined_raft_net_invariant_do_generic_server requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    find_copy_apply_lem_hyp doGenericServer_packets. subst. simpl in *.
    find_apply_hyp_hyp. break_or_hyp.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    find_apply_lem_hyp doGenericServer_log_type_term_votesReceived;
    break_and; repeat find_rewrite; eauto. intuition.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_reboot :
    refined_raft_net_invariant_reboot requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; congruence.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    subst. repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma requestVote_maxIndex_maxTerm_init :
    refined_raft_net_invariant_init requestVote_maxIndex_maxTerm.
  Proof.
    red. unfold requestVote_maxIndex_maxTerm. intros. simpl in *.
    intuition.
  Qed.

  Instance rvmimti : requestVote_maxIndex_maxTerm_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply requestVote_maxIndex_maxTerm_init.
  - apply requestVote_maxIndex_maxTerm_client_request.
  - apply requestVote_maxIndex_maxTerm_timeout.
  - apply requestVote_maxIndex_maxTerm_append_entries.
  - apply requestVote_maxIndex_maxTerm_append_entries_reply.
  - apply requestVote_maxIndex_maxTerm_request_vote.
  - apply requestVote_maxIndex_maxTerm_request_vote_reply.
  - apply requestVote_maxIndex_maxTerm_do_leader.
  - apply requestVote_maxIndex_maxTerm_do_generic_server.
  - apply requestVote_maxIndex_maxTerm_state_same_packet_subset.
  - apply requestVote_maxIndex_maxTerm_reboot.
  Qed.
  
End RequestVoteMaxIndexMaxTerm.
