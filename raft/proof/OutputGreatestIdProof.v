Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import TraceRelations.

Require Import Raft.
Require Import CommonTheorems.
Require Import LogMatchingInterface.
Require Import StateMachineSafetyInterface.
Require Import AppliedEntriesMonotonicInterface.
Require Import MaxIndexSanityInterface.
Require Import TraceUtil.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SortedInterface.

Require Import OutputGreatestIdInterface.

Section OutputGreatestId.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lmi : log_matching_interface}.
  Context {si : sorted_interface}.
  Context {aemi : applied_entries_monotonic_interface}.
  Context {smsi : state_machine_safety_interface}.
  Context {misi : max_index_sanity_interface}.

  Instance ogii : output_greatest_id_interface.
  Proof.
  Admitted.
End OutputGreatestId.
