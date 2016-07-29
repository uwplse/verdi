Require Import GhostSimulations.

Require Import Raft.
Require Import RefinementSpecLemmas.
Require Import RaftRefinementInterface.
Require Import RaftMsgRefinementInterface.

Require Import InLogInAllEntriesInterface.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import GhostLogAllEntriesInterface.

Section GhostLogAllEntriesProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rmri : raft_msg_refinement_interface}.
  Context {iliaei : in_log_in_all_entries_interface}.

  Definition lifted_in_log_in_all_entries (net : network) :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      exists t,
        In (t, e) (allEntries (fst (nwState net h))).

  Lemma lifted_in_log_in_all_entries_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_in_log_in_all_entries net.
  Proof.
    intros.
    unfold lifted_in_log_in_all_entries; intros.
    find_eapply_lem_hyp msg_lift_prop;
      [|intros; eapply in_log_in_all_entries_invariant; eauto].
    simpl in *.
    unfold in_log_in_all_entries in *.
    unfold mgv_deghost in *.
    simpl in *.
    repeat break_match; simpl in *; eauto.
  Qed.

  Lemma update_elections_data_appendEntries_preserves_allEntries' :
    forall st h t n pli plt es ci x,
      In x (allEntries (fst st)) ->
      In x (allEntries (update_elections_data_appendEntries h st t n pli plt es ci)).
  Proof.
    unfold update_elections_data_appendEntries.
    intros. break_let. break_match; auto.
    break_if; auto.
    simpl. intuition.
  Qed.

  Lemma ghost_log_allEntries_append_entries :
    msg_refined_raft_net_invariant_append_entries' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - repeat find_rewrite.
      find_apply_hyp_hyp; intuition; eauto.
      + eapply_prop_hyp In In; eauto.
        break_exists_exists.
        eauto using update_elections_data_appendEntries_preserves_allEntries'.
      + remember (pSrc p0).
        subst. simpl in *.
        unfold write_ghost_log in *.
        simpl in *.
        match goal with
        | [ H : In _ (log ?d), H' : context [handleAppendEntries ?h],
            H'' : msg_refined_raft_intermediate_reachable ?net |- _ ] =>
          replace d with (snd (nwState net h)) in * by
              (simpl; find_higher_order_rewrite; rewrite_update; auto)
        end.
        find_eapply_lem_hyp lifted_in_log_in_all_entries_invariant; eauto.
        break_exists_exists.
        simpl in *. find_higher_order_rewrite. rewrite_update. simpl in *.
        auto.
    - find_apply_hyp_hyp; intuition; eauto.
      subst. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_apply_hyp_hyp; intuition; eauto.
      + eapply_prop_hyp In In;
        repeat find_rewrite; eauto.
      + do_in_map.
        subst. simpl in *. unfold add_ghost_msg in *.
        do_in_map. subst. simpl in *. unfold write_ghost_log in *.
        pose proof lifted_in_log_in_all_entries_invariant (mkNetwork _ _) ltac:(eauto) (pDst p) e.
        simpl in *. find_higher_order_rewrite. rewrite_update.
        simpl in *. auto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      subst. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_request_vote :
    msg_refined_raft_net_invariant_request_vote' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - rewrite update_elections_data_requestVote_allEntries.
      find_apply_hyp_hyp; intuition; eauto.
      + eapply_prop_hyp In In;
        repeat find_rewrite; eauto.
      + subst. simpl in *. unfold write_ghost_log in *.
        pose proof lifted_in_log_in_all_entries_invariant (mkNetwork _ _) ltac:(eauto) (pDst p) e.
        simpl in *. find_higher_order_rewrite. rewrite_update.
        simpl in *. concludes. break_exists_exists.
        find_rewrite_lem update_elections_data_requestVote_allEntries.
        auto.
    - find_apply_hyp_hyp; intuition; eauto.
      subst. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    rewrite update_elections_data_requestVoteReply_allEntries.
    repeat find_rewrite.
    find_apply_hyp_hyp.
    eauto.
  Qed.

  Lemma ghost_log_allEntries_timeout :
    msg_refined_raft_net_invariant_timeout' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - rewrite update_elections_data_timeout_allEntries.
      find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. unfold add_ghost_msg in *.
      do_in_map. subst. simpl in *. unfold write_ghost_log in *.
      pose proof lifted_in_log_in_all_entries_invariant (mkNetwork _ _) ltac:(eauto) n e.
      simpl in *. find_higher_order_rewrite. rewrite_update.
      simpl in *. concludes. break_exists_exists.
      find_rewrite_lem update_elections_data_timeout_allEntries. auto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_client_request :
    msg_refined_raft_net_invariant_client_request' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_apply_hyp_hyp.
      intuition.
      + eapply_prop_hyp In In; eauto.
        break_exists_exists.
        eauto using update_elections_data_clientRequest_allEntries_old'.
      + do_in_map. unfold add_ghost_msg in *. do_in_map.
        subst x. simpl in *. destruct p. simpl in *. find_inversion.
        simpl in *. unfold write_ghost_log in *.
        pose proof lifted_in_log_in_all_entries_invariant (mkNetwork _ _) ltac:(eauto) pSrc e.
        simpl in *. find_higher_order_rewrite. rewrite_update.
        simpl in *. concludes. break_exists_exists.
        auto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_do_leader :
    msg_refined_raft_net_invariant_do_leader' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. unfold add_ghost_msg in *.
      do_in_map. subst. simpl in *. unfold write_ghost_log in *.
      pose proof lifted_in_log_in_all_entries_invariant (mkNetwork _ _) ltac:(eauto) n e.
      simpl in *. find_higher_order_rewrite. rewrite_update.
      simpl in *. concludes. auto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server' ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. unfold add_ghost_msg in *.
      do_in_map. subst. simpl in *. unfold write_ghost_log in *.
      pose proof lifted_in_log_in_all_entries_invariant (mkNetwork _ _) ltac:(eauto) n e.
      simpl in *. find_higher_order_rewrite. rewrite_update.
      simpl in *. concludes. auto.
    - find_apply_hyp_hyp; intuition; eauto.
      do_in_map.
      remember (pSrc p).
      subst p. simpl in *. congruence.
  Qed.

  Lemma ghost_log_allEntries_reboot :
    msg_refined_raft_net_invariant_reboot ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.
  
  Lemma ghost_log_allEntries_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_apply_hyp_hyp.
    repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.
  
  Lemma ghost_log_allEntries_init :
    msg_refined_raft_net_invariant_init ghost_log_allEntries.
  Proof.
    red. unfold ghost_log_allEntries. intros. simpl in *.
    intuition.
  Qed.
  
  Instance glaei : ghost_log_allEntries_interface.
  Proof.
    split.
    intros.
    apply msg_refined_raft_net_invariant'; auto.
    - apply ghost_log_allEntries_init.
    - apply ghost_log_allEntries_client_request.
    - apply ghost_log_allEntries_timeout.
    - apply ghost_log_allEntries_append_entries.
    - apply ghost_log_allEntries_append_entries_reply.
    - apply ghost_log_allEntries_request_vote.
    - apply msg_refined_raft_net_invariant_request_vote_reply'_weak.
      apply ghost_log_allEntries_request_vote_reply.
    - apply ghost_log_allEntries_do_leader.
    - apply ghost_log_allEntries_do_generic_server.
    - apply msg_refined_raft_net_invariant_subset'_weak.
      apply ghost_log_allEntries_state_same_packet_subset.
    - apply msg_refined_raft_net_invariant_reboot'_weak.
      apply ghost_log_allEntries_reboot.
  Qed.
End GhostLogAllEntriesProof.
