Require Import List.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonTheorems.
Require Import CommitRecordedCommittedInterface.
Require Import StateMachineSafetyInterface.
Require Import StateMachineSafetyPrimeInterface.
Require Import RaftRefinementInterface.


Section StateMachineSafetyProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {crci : commit_recorded_committed_interface}.
  Context {smspi : state_machine_safety'interface}.
  
  Lemma exists_deghost_packet : 
    forall net p,
      In p (nwPackets (deghost net)) ->
      exists (q : packet (params := raft_refined_multi_params)),
        In q (nwPackets net) /\ p = deghost_packet q.
  Proof.
    intros.
    unfold deghost in *. simpl in *. do_in_map.
    subst. eexists; eauto.
  Qed.

  Lemma state_machine_safety_deghost :
    forall net,
      refined_raft_intermediate_reachable net ->
      state_machine_safety (deghost net).
  Proof.
    intros. unfold state_machine_safety in *. intuition.
    - unfold state_machine_safety_host. intros.
      do 2 (find_apply_lem_hyp commit_recorded_committed_invariant; auto).
      find_apply_lem_hyp state_machine_safety'_invariant.
      unfold state_machine_safety' in *. intuition. eauto.
    - unfold state_machine_safety_nw. intros.
      find_apply_lem_hyp commit_recorded_committed_invariant; auto.
      find_apply_lem_hyp state_machine_safety'_invariant.
      unfold state_machine_safety', state_machine_safety_nw' in *. intuition.
      find_apply_lem_hyp exists_deghost_packet. break_exists.
      intuition. subst. simpl in *. repeat break_match. simpl in *.
      subst. eapply H5 in H1; repeat find_rewrite; simpl; eauto.
  Qed.

  Theorem state_machine_safety_invariant :
    forall net,
      raft_intermediate_reachable net ->
      state_machine_safety net.
  Proof.
    intros.
    eapply lower_prop; intros; auto.
    apply state_machine_safety_deghost; auto.
  Qed.
      
  Instance smsi : state_machine_safety_interface.
  Proof.
    split.
    exact state_machine_safety_invariant.
  Qed.
End StateMachineSafetyProof.
