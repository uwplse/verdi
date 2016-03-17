Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import Raft.

Section MatchIndexSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition match_index_sanity net :=
    forall leader h,
      type (nwState net leader) = Leader ->
      assoc_default name_eq_dec (matchIndex (nwState net leader)) h 0 <=
      maxIndex (log (nwState net leader)).

  Class match_index_sanity_interface : Prop :=
    {
      match_index_sanity_invariant :
        forall net,
          raft_intermediate_reachable net ->
          match_index_sanity net
    }.
  
End MatchIndexSanity.
