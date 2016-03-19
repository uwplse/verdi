Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesIndicesGt0.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition allEntries_indices_gt_0 (net : network) : Prop := 
    forall h e,
      In e (map snd (allEntries (fst (nwState net h)))) ->
      eIndex e > 0.

  Class allEntries_indices_gt_0_interface : Prop :=
    {
      allEntries_indices_gt_0_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_indices_gt_0 net
    }.
End AllEntriesIndicesGt0.
