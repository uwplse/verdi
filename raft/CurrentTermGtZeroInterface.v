Require Import List.

Require Import Net.
Require Import Raft.

Require Import CommonDefinitions.

Section CurrentTermGtZeroInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition current_term_gt_zero (net : network) :=
    forall h,
      type (nwState net h) <> Follower ->
      1 <= currentTerm (nwState net h).

  Class current_term_gt_zero_interface : Prop := {
    current_term_gt_zero_invariant : forall net,
      raft_intermediate_reachable net ->
      current_term_gt_zero net
  }.
End CurrentTermGtZeroInterface.
