Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import StateMachineCorrectInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Raft.
Require Import CommonDefinitions.

Section StateMachineCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem state_machine_correct_invariant :
    forall net,
      raft_intermediate_reachable net ->
      state_machine_correct net.
  Admitted.

  Instance smci : state_machine_correct_interface.
  Proof.
    split.
    exact state_machine_correct_invariant.
  Qed.
End StateMachineCorrect.