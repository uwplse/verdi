Require Import Raft.

Section MaxIndexSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition maxIndex_lastApplied net :=
    forall h,
      lastApplied (nwState net h) <= maxIndex (log (nwState net h)).

  Definition maxIndex_commitIndex net :=
    forall h,
      commitIndex (nwState net h) <= maxIndex (log (nwState net h)).

  Definition maxIndex_sanity net :=
    maxIndex_lastApplied net /\ maxIndex_commitIndex net.

  Class max_index_sanity_interface : Prop :=
    {
      max_index_sanity_invariant :
        forall net,
          raft_intermediate_reachable net ->
          maxIndex_sanity net
    }.
End MaxIndexSanity.
