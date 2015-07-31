Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import RaftMsgRefinementInterface.

Require Import NextIndexSafetyInterface.
Require Import RefinedLogMatchingLemmasInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import GhostLogCorrectInterface.

Section GhostLogCorrectProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rmri : raft_msg_refinement_interface}.
  Context {nisi : nextIndex_safety_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  
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

  Definition lifted_nextIndex_safety net : Prop :=
    forall h h',
      type (snd (nwState net h)) = Leader ->
      pred (getNextIndex (snd (nwState net h)) h') <= maxIndex (log (snd (nwState net h))).
  
  Lemma lifted_nextIndex_safety_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_nextIndex_safety net.
  Proof.
    intros.
    enough (nextIndex_safety (deghost (mgv_deghost net))) by
        (unfold nextIndex_safety, lifted_nextIndex_safety, deghost, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop_all_the_way; eauto using nextIndex_safety_invariant.
  Qed.

  Definition lifted_entries_contiguous net :=
    forall h,
      contiguous_range_exact_lo (log (snd (nwState net h))) 0.

  Definition lifted_entries_sorted net :=
    forall h,
      sorted (log (snd (nwState net h))).
  
  Lemma lifted_entries_contiguous_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_contiguous net.
  Proof.
    intros.
    enough (entries_contiguous (mgv_deghost net)) by
        (unfold entries_contiguous, lifted_entries_contiguous, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop; eauto using entries_contiguous_invariant.
  Qed.

  Lemma lifted_entries_sorted_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_sorted net.
  Proof.
    intros.
    enough (entries_sorted (mgv_deghost net)) by
        (unfold entries_sorted, lifted_entries_sorted, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop; eauto using entries_sorted_invariant.
  Qed.
  
  Lemma ghost_log_correct_append_entries :
    msg_refined_raft_net_invariant_append_entries ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    find_apply_hyp_hyp; intuition; eauto.
    subst. simpl in *.
    subst.
    find_apply_lem_hyp handleAppendEntries_not_append_entries.
    intuition. find_false.
    repeat eexists; eauto.
  Qed.

  Lemma ghost_log_correct_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    find_apply_hyp_hyp; intuition; eauto.
    subst. simpl in *.
    subst.
    find_apply_lem_hyp handleAppendEntriesReply_packets.
    subst. simpl in *. intuition.
  Qed.

  Lemma ghost_log_correct_request_vote :
    msg_refined_raft_net_invariant_request_vote ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    find_apply_hyp_hyp; intuition; eauto.
    subst. simpl in *.
    subst.
    find_apply_lem_hyp handleRequestVote_no_append_entries.
    intuition. find_false.
    repeat eexists; eauto.
  Qed.

  Lemma ghost_log_correct_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    find_apply_hyp_hyp; intuition; eauto.
  Qed.

  Lemma doLeader_replicaMessage :
    forall h st os st' ms m,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      type st = Leader /\
      exists h',
        m = replicaMessage st' h h'.
  Proof.
    unfold doLeader in *.
    intros; repeat break_match; find_inversion; simpl in *; intuition.
    do_in_map. eauto.
  Qed.


  Lemma doLeader_getNextIndex :
    forall h h' st os st' ms,
      doLeader st h = (os, st', ms) ->
      getNextIndex st' h' = getNextIndex st h'.
  Proof.
    intros.
    unfold getNextIndex, doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.
  
  Lemma ghost_log_correct_do_leader :
    msg_refined_raft_net_invariant_do_leader ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    find_apply_hyp_hyp; intuition; eauto.
    do_in_map.
    subst. simpl in *.
    unfold add_ghost_msg in *. do_in_map. subst. simpl in *.
    find_eapply_lem_hyp doLeader_replicaMessage; eauto.
    break_and.
    break_exists. subst.
    unfold replicaMessage in *.
    simpl in *. find_inversion.
    unfold write_ghost_log. simpl.
    match goal with
      | |- context [pred ?x] =>
        remember (pred x) as index
    end.
    destruct index.
    - left. intuition; eauto.
      + break_match; intuition.
        find_apply_lem_hyp findAtIndex_elim.
        intuition.
        find_erewrite_lem doLeader_log; eauto.
        enough (0 < eIndex e) by omega.
        eapply lifted_entries_contiguous_invariant; eauto.
      + erewrite doLeader_log; eauto.
        apply sorted_findGtIndex_0; [|eapply lifted_entries_sorted_invariant; eauto].
        intros. eapply lifted_entries_contiguous_invariant; eauto.
    - right.
      erewrite doLeader_log; eauto.
      enough (exists e, findAtIndex (log (snd (nwState net leaderId))) (S index) = Some e) by
          (break_exists_name e;
           find_copy_apply_lem_hyp findAtIndex_elim; intuition;
           auto;
           exists e; intuition;
             do 2 (unfold raft_data in *; simpl in *);
             repeat find_rewrite; auto).
      eapply contiguous_findAtIndex;
        [eapply lifted_entries_sorted_invariant; eauto|
         eapply lifted_entries_contiguous_invariant; eauto|].
      intuition.
      repeat find_rewrite. 
      erewrite doLeader_getNextIndex; eauto.
      eapply lifted_nextIndex_safety_invariant; eauto.
  Qed.

  Lemma ghost_log_correct_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    find_apply_hyp_hyp; intuition; eauto.
    find_apply_lem_hyp doGenericServer_packets.
    subst. simpl in *. intuition.
  Qed.

  Lemma ghost_log_correct_reboot :
    msg_refined_raft_net_invariant_reboot ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_reverse_rewrite. eauto.
  Qed.

  Lemma ghost_log_correct_client_request :
    msg_refined_raft_net_invariant_client_request ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    find_apply_hyp_hyp; intuition; eauto.
    subst. simpl in *.
    subst.
    find_apply_lem_hyp handleClientRequest_packets.
    subst. simpl in *. intuition.
  Qed.

  Lemma ghost_log_correct_timeout :
    msg_refined_raft_net_invariant_timeout ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    find_apply_hyp_hyp; intuition; eauto.
    exfalso.
    subst. simpl in *.
    subst. do_in_map. subst.
    simpl in *. unfold add_ghost_msg in *.
    do_in_map. subst. simpl in *.
    find_eapply_lem_hyp handleTimeout_packets; eauto.
    repeat find_rewrite. intuition. find_false.
    repeat eexists; eauto.
  Qed.

  Lemma ghost_log_correct_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    eauto.
  Qed.

  Lemma ghost_log_correct_init :
    msg_refined_raft_net_invariant_init ghost_log_correct.
  Proof.
    red. unfold ghost_log_correct. intros. simpl in *.
    intuition.
  Qed.
  
  Instance glci : ghost_log_correct_interface.
  Proof.
    split. intros.
    apply msg_refined_raft_net_invariant; auto.
    - apply ghost_log_correct_init.
    - apply ghost_log_correct_client_request.
    - apply ghost_log_correct_timeout.
    - apply ghost_log_correct_append_entries.
    - apply ghost_log_correct_append_entries_reply.
    - apply ghost_log_correct_request_vote.
    - apply ghost_log_correct_request_vote_reply.
    - apply ghost_log_correct_do_leader.
    - apply ghost_log_correct_do_generic_server.
    - apply ghost_log_correct_state_same_packet_subset.
    - apply ghost_log_correct_reboot.
  Qed.
  
End GhostLogCorrectProof.
