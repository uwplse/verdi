Require Import Raft.
Require Import RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import CommonTheorems.

Require Import RequestVoteMaxIndexMaxTermInterface.
Require Import RequestVoteReplyTermSanityInterface.
Require Import VotedForMoreUpToDateInterface.

Require Import RequestVoteReplyMoreUpToDateInterface.

Section RequestVoteReplyMoreUpToDate.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {rvmimti : requestVote_maxIndex_maxTerm_interface}.
  Context {rvrtsi : requestVoteReply_term_sanity_interface}.
  Context {vfmutdi : votedFor_moreUpToDate_interface}.

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

  
  
  Lemma requestVoteReply_moreUpToDate_append_entries :
    refined_raft_net_invariant_append_entries requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    assert (In p0 (nwPackets net)) by
        (find_apply_hyp_hyp; repeat find_rewrite; intuition; [in_crush|];
         exfalso; subst; simpl in *; subst;
         unfold handleAppendEntries in *;
           repeat break_match; find_inversion).
    repeat find_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_append_entries; eauto;
    find_apply_lem_hyp handleAppendEntries_log_term_type;
    intuition; repeat find_rewrite; try congruence;
    eauto.
  Qed.

  Lemma requestVoteReply_moreUpToDate_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    assert (In p0 (nwPackets net)) by
        (repeat find_rewrite;
         find_apply_lem_hyp handleAppendEntriesReply_packets;
         subst; simpl in *; find_apply_hyp_hyp; intuition; in_crush).
    repeat find_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_votesReceived.
    find_copy_apply_lem_hyp handleAppendEntriesReply_log_term_type.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    intuition; try congruence; repeat find_rewrite; eauto.
  Qed.
  
  Lemma requestVoteReply_moreUpToDate_request_vote :
    refined_raft_net_invariant_request_vote requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    find_copy_apply_lem_hyp handleRequestVote_votesReceived.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto. 
    - find_copy_apply_lem_hyp handleRequestVote_log_term_type; intuition; try congruence.
      repeat find_rewrite.
      find_apply_hyp_hyp. intuition.
      + assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
        repeat find_rewrite.
        eapply_prop_hyp pBody pBody; eauto.
        break_exists_exists. intuition.
        eauto using update_elections_data_request_vote_votesWithLog_old.
      + remember (pSrc p0) as h.
        subst. simpl in *. subst.
        find_copy_apply_lem_hyp handleRequestVote_reply_true.
        find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto;
        intuition; eauto; repeat find_rewrite.
        * find_eapply_lem_hyp votedFor_moreUpToDate_invariant; eauto.
          repeat conclude_using eauto.
          break_exists_exists; intuition; eauto using update_elections_data_request_vote_votesWithLog_old.
        * find_apply_lem_hyp requestVote_maxIndex_maxTerm_invariant.
          eapply_prop_hyp requestVote_maxIndex_maxTerm pBody; eauto.
          concludes. intuition; subst.
          eexists; intuition; eauto.
    - find_copy_apply_lem_hyp handleRequestVote_log_term_type; intuition; try congruence.
      repeat find_rewrite.
      find_apply_hyp_hyp. intuition.
      + assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
        repeat find_rewrite.
        eapply_prop_hyp pBody pBody; eauto.
      + remember (pDst p0) as h.
        subst. simpl in *. subst.
        find_copy_apply_lem_hyp handleRequestVote_reply_true. intuition.
    - find_apply_hyp_hyp; intuition.
      + assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
        repeat find_rewrite.
        eapply_prop_hyp pBody pBody; eauto.
        break_exists_exists. intuition.
        eauto using update_elections_data_request_vote_votesWithLog_old.
      + remember (pSrc p0) as h.
        subst. simpl in *. subst.
        find_copy_apply_lem_hyp handleRequestVote_reply_true. intuition.
        find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto.
        intuition; repeat find_rewrite; eauto.
        * find_copy_apply_lem_hyp votedFor_moreUpToDate_invariant.
          eapply_prop_hyp votedFor_moreUpToDate RaftState.votedFor; eauto.
          concludes.
          break_exists_exists; intuition; eauto using update_elections_data_request_vote_votesWithLog_old.
        * find_apply_lem_hyp requestVote_maxIndex_maxTerm_invariant.
          eapply_prop_hyp requestVote_maxIndex_maxTerm pBody; eauto.
          concludes. intuition; subst.
          eexists; intuition; eauto.
    - find_apply_hyp_hyp. intuition.
      + assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
        repeat find_rewrite.
        eapply_prop_hyp pBody pBody; eauto.
      + subst. simpl in *. subst. simpl in *.
        find_copy_apply_lem_hyp handleRequestVote_reply_true. intuition.
  Qed.

  Lemma requestVoteReply_moreUpToDate_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - erewrite handleRequestVoteReply_log; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
      intuition.
      repeat find_rewrite.
      rewrite update_elections_data_request_vote_reply_votesWithLog.
      eauto.
    - erewrite handleRequestVoteReply_log; eauto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_log_term_type; eauto.
      intuition.
      repeat find_rewrite. eauto.
    - rewrite update_elections_data_request_vote_reply_votesWithLog.
      eauto.
  Qed.

  Lemma requestVoteReply_moreUpToDate_timeout :
    refined_raft_net_invariant_timeout requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
      intuition; try congruence.
      repeat find_rewrite. simpl in *. intuition. subst.
      exists (log d). intuition. auto using moreUpToDate_refl.
    - find_copy_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
      intuition; try congruence.
      repeat find_rewrite. simpl in *.
      find_eapply_lem_hyp requestVoteReply_term_sanity_invariant; eauto;
      unfold raft_data in *; simpl in *;
      unfold raft_data in *; simpl in *; try omega; [idtac].
      find_apply_hyp_hyp. intuition.
      exfalso.
      do_in_map.
      remember (pDst p) as h. subst p. simpl in *.
      unfold handleTimeout, tryToBecomeLeader in *.
      repeat break_match; find_inversion; simpl in *; intuition.
    - find_apply_hyp_hyp.
      intuition.
      + eapply_prop_hyp pBody pBody; eauto.
        break_exists_exists; intuition; eauto using update_elections_data_timeout_votesWithLog_old.
      + exfalso.
        do_in_map. remember (pSrc p).
        subst p. simpl in *.
        unfold handleTimeout, tryToBecomeLeader in *.
        repeat break_match; find_inversion; simpl in *; intuition;
        do_in_map; subst; simpl in *; congruence.
    - find_apply_hyp_hyp.
      intuition.
      + eapply_prop_hyp pBody pBody; eauto.
      + exfalso.
        do_in_map. remember (pSrc p).
        subst p. simpl in *.
        unfold handleTimeout, tryToBecomeLeader in *.
        repeat break_match; find_inversion; simpl in *; intuition;
        do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma requestVoteReply_moreUpToDate_client_request :
    refined_raft_net_invariant_client_request requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    find_copy_apply_lem_hyp handleClientRequest_packets.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite votesWithLog_same_client_request; eauto;
    find_apply_lem_hyp handleClientRequest_candidate; subst; eauto.
  Qed.

  Lemma requestVoteReply_moreUpToDate_do_leader :
    refined_raft_net_invariant_do_leader requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
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
  
  Lemma requestVoteReply_moreUpToDate_do_generic_server :
    refined_raft_net_invariant_do_generic_server requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
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

  Lemma requestVoteReply_moreUpToDate_reboot :
    refined_raft_net_invariant_reboot requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto; congruence.
  Qed.

  Lemma requestVoteReply_moreUpToDate_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    subst. repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma requestVoteReply_moreUpToDate_init :
    refined_raft_net_invariant_init requestVoteReply_moreUpToDate.
  Proof.
    red. unfold requestVoteReply_moreUpToDate. intros. simpl in *.
    intuition.
  Qed.
  
  Instance rvrmutdi : requestVoteReply_moreUpToDate_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply requestVoteReply_moreUpToDate_init.
  - apply requestVoteReply_moreUpToDate_client_request.
  - apply requestVoteReply_moreUpToDate_timeout.
  - apply requestVoteReply_moreUpToDate_append_entries.
  - apply requestVoteReply_moreUpToDate_append_entries_reply.
  - apply requestVoteReply_moreUpToDate_request_vote.
  - apply requestVoteReply_moreUpToDate_request_vote_reply.
  - apply requestVoteReply_moreUpToDate_do_leader.
  - apply requestVoteReply_moreUpToDate_do_generic_server.
  - apply requestVoteReply_moreUpToDate_state_same_packet_subset.
  - apply requestVoteReply_moreUpToDate_reboot.
  Qed.
  
End RequestVoteReplyMoreUpToDate.
