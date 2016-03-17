Require Import List.
Import ListNotations.

Require Import Net.
Require Import StructTact.Util.
Require Import StructTact.StructTactics.
Require Import CommonDefinitions.

Require Import Raft.

Section LastAppliedLeCommitIndexInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition lastApplied_le_commitIndex net :=
    forall h,
      lastApplied (nwState net h) <= commitIndex (nwState net h).

  Class lastApplied_le_commitIndex_interface : Prop :=
    {
      lastApplied_le_commitIndex_invariant :
        forall net,
          raft_intermediate_reachable net ->
          lastApplied_le_commitIndex net
    }.
End LastAppliedLeCommitIndexInterface.
