Require Import Raft.
Require Import RaftRefinementInterface.

Section VotesLeCurrentTermInterface.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition votes_le_currentTerm net :=
    forall h t n,
      In (t, n) (votes (fst (nwState net h))) ->
      t <= currentTerm (snd (nwState net h)).

  Class votes_le_current_term_interface : Prop :=
    {
      votes_le_current_term_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          votes_le_currentTerm net
    }.
End VotesLeCurrentTermInterface.
