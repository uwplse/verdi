Require Import Raft.
Require Import RaftRefinementInterface.

Section MatchIndexAllEntries.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition match_index_all_entries net :=
    forall e leader h,
      type (snd (nwState net leader)) = Leader ->
      eIndex e <= assoc_default name_eq_dec (matchIndex (snd (nwState net leader))) h 0 ->
      In e (log (snd (nwState net leader))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In (eTerm e, e) (allEntries (fst (nwState net h))).

  Class match_index_all_entries_interface : Prop :=
    {
      match_index_all_entries_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          match_index_all_entries net
    }.
  
End MatchIndexAllEntries.
