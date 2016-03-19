Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section AllEntriesTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition allEntries_term_sanity net :=
    forall t e h,
      In (t, e) (allEntries (fst (nwState net h))) ->
      t <= currentTerm (snd (nwState net h)).

  Class allEntries_term_sanity_interface : Prop :=
    {
      allEntries_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_term_sanity net
    }.
End AllEntriesTermSanity.
