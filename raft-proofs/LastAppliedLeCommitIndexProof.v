Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Require Import Raft.

Require Import LastAppliedLeCommitIndexInterface.
Require Import UpdateLemmas.
Require Import SpecLemmas.
Require Import CommonTheorems.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.


Section LastAppliedLeCommitIndex.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


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

  Lemma lastApplied_le_commitIndex_appendEntries :
    raft_net_invariant_append_entries lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
    repeat find_rewrite.
    find_apply_lem_hyp handleAppendEntries_log_detailed.
    intuition; repeat find_rewrite; eauto;
    eapply le_trans; eauto; eauto using Max.le_max_l.
  Qed.

  Lemma lastApplied_le_commitIndex_appendEntriesReply :
    raft_net_invariant_append_entries_reply lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleAppendEntriesReply_same_lastApplied.
    repeat find_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_same_commitIndex.
    repeat find_rewrite. eauto.
  Qed.

  
  Lemma lastApplied_le_commitIndex_requestVote :
    raft_net_invariant_request_vote lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleRequestVote_same_lastApplied.
    repeat find_rewrite.
    find_copy_apply_lem_hyp handleRequestVote_same_commitIndex.
    repeat find_rewrite. eauto.
  Qed.

  Lemma lastApplied_le_commitIndex_requestVoteReply :
    raft_net_invariant_request_vote_reply lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    rewrite handleRequestVoteReply_same_lastApplied.
    rewrite handleRequestVoteReply_same_commitIndex. eauto.
  Qed.


  Lemma doLeader_same_lastApplied:
    forall st (os : list raft_output) (d' : raft_data)
      (ms : list (name * msg)) (h0 : name),
      doLeader st h0 = (os, d', ms) ->
      lastApplied d' = lastApplied st.
  Proof.
    intros.
    unfold doLeader, advanceCommitIndex in *.
    repeat break_match; simpl in *; find_inversion; auto.
  Qed.

  Lemma fold_left_max :
    forall l y z,
      (forall x, In x l ->
            y <= x) ->
      y <= z ->
      y <= fold_left max l z.
  Proof.
    induction l; simpl in *; auto.
    intros.
    specialize (IHl y (max z a)).
    forward IHl; eauto. concludes.
    forward IHl; [eapply le_trans; eauto; eauto using Max.le_max_l|].
    concludes. auto.
  Qed.
  
  Lemma advanceCommitIndex_commitIndex :
    forall st h,
      commitIndex st <= commitIndex (advanceCommitIndex st h).
  Proof.
    intros. unfold advanceCommitIndex. simpl in *.
    apply fold_left_max; auto.
    intros.
    do_in_map. subst.
    find_apply_lem_hyp filter_In.
    repeat (intuition; do_bool).
  Qed.
  
  Lemma doLeader_same_commitIndex :
    forall st (os : list raft_output) (d' : raft_data)
      (ms : list (name * msg)) (h0 : name),
      doLeader st h0 = (os, d', ms) ->
      commitIndex st <= commitIndex d'.
  Proof.
    intros.
    unfold doLeader in *.
    repeat break_match; tuple_inversion; auto; eauto using advanceCommitIndex_commitIndex.
    eapply le_trans; [eapply advanceCommitIndex_commitIndex with (h := h0)|]; eauto.
  Qed.
  
  Lemma lastApplied_le_commitIndex_doLeader :
    raft_net_invariant_do_leader lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    subst.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp doLeader_same_lastApplied.
    find_copy_apply_lem_hyp doLeader_same_commitIndex.
    repeat find_rewrite. eapply le_trans; [|eauto]; eauto.
  Qed.
  
  Lemma doGenericServer_lastApplied:
    forall (h : name) 
      (st : raft_data) (out : list raft_output) (st' : raft_data)
      (ms : list (name * msg)),
      doGenericServer h st = (out, st', ms) ->
      lastApplied st' <= max (lastApplied st) (commitIndex st).
  Proof.
    intros. unfold doGenericServer in *. break_let. find_inversion.
    simpl in *.
    break_if; simpl in *; do_bool; auto.
    - use_applyEntries_spec. subst. simpl in *.
      eauto using Max.le_max_r.
    - use_applyEntries_spec. subst. simpl in *.
      eauto using Max.le_max_l.
  Qed.

  Lemma lastApplied_le_commitIndex_doGenericServer :
    raft_net_invariant_do_generic_server lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    subst.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp doGenericServer_commitIndex.
    find_copy_apply_lem_hyp doGenericServer_lastApplied.
    repeat find_rewrite.
    erewrite Max.max_r in *; eauto.
  Qed.

  Lemma lastApplied_le_commitIndex_clientRequest :
    raft_net_invariant_client_request lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    subst.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleClientRequest_commitIndex.
    find_copy_apply_lem_hyp handleClientRequest_lastApplied.
    repeat find_rewrite. eauto.
  Qed.
  

  Lemma lastApplied_le_commitIndex_timeout :
    raft_net_invariant_timeout lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    subst.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleTimeout_commitIndex.
    find_copy_apply_lem_hyp handleTimeout_lastApplied.
    repeat find_rewrite. eauto.
  Qed.

  Lemma lastApplied_le_commitIndex_reboot :
    raft_net_invariant_reboot lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    subst.
    simpl in *. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.

  Lemma lastApplied_le_commitIndex_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    subst.
    simpl in *. repeat find_reverse_higher_order_rewrite. auto.
  Qed.

  Lemma lastApplied_le_commitIndex_init :
    raft_net_invariant_init lastApplied_le_commitIndex.
  Proof.
    red. unfold lastApplied_le_commitIndex. intros.
    simpl in *. auto.
  Qed.

  Theorem lastApplied_le_commitIndex_invariant :
    forall net,
      raft_intermediate_reachable net ->
      lastApplied_le_commitIndex net.
  Proof.
    intros. apply raft_net_invariant; auto.
    - apply lastApplied_le_commitIndex_init.
    - apply lastApplied_le_commitIndex_clientRequest.
    - apply lastApplied_le_commitIndex_timeout.
    - apply lastApplied_le_commitIndex_appendEntries.
    - apply lastApplied_le_commitIndex_appendEntriesReply.
    - apply lastApplied_le_commitIndex_requestVote.
    - apply lastApplied_le_commitIndex_requestVoteReply.
    - apply lastApplied_le_commitIndex_doLeader.
    - apply lastApplied_le_commitIndex_doGenericServer.
    - apply lastApplied_le_commitIndex_state_same_packet_subset.
    - apply lastApplied_le_commitIndex_reboot.
  Qed.
  
  Instance lalcii : lastApplied_le_commitIndex_interface.
  split. auto using lastApplied_le_commitIndex_invariant.
  Qed.

End LastAppliedLeCommitIndex.

