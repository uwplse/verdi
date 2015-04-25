Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import Raft.
Require Import VerdiTactics.

Require Import SortedInterface.

Require Import CommonTheorems.

Require Import UniqueIndicesInterface.

Section UniqueIndices.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {si : sorted_interface}.

  Theorem UniqueIndices_invariant :
    forall net,
      raft_intermediate_reachable net ->
      UniqueIndices net.
  Proof.
    intros.
    find_apply_lem_hyp logs_sorted_invariant.
    unfold logs_sorted, UniqueIndices in *. intuition.
    - unfold uniqueIndices_host_invariant, logs_sorted_host in *.
      eauto using sorted_uniqueIndices.
    - unfold uniqueIndices_nw_invariant, logs_sorted_nw in *.
      eauto using sorted_uniqueIndices.
  Qed.

  Instance uii : unique_indices_interface.
  Proof.
    split.
    exact UniqueIndices_invariant.
  Qed.
End UniqueIndices.
