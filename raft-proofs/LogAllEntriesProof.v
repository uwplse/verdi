Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.
Require Import RefinementCommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LogAllEntriesInterface.

Section LogAllEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Instance laei : log_all_entries_interface.
  Admitted.
End LogAllEntries.