Require Import RaftRefinementInterface.
Require Import Raft.

Section CroniesTermInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition cronies_term (net : network) :=
    forall h h' t,
      In h (cronies (fst (nwState net h')) t) ->
      t <= currentTerm (snd (nwState net h')).

  Class cronies_term_interface : Prop :=
    {
      cronies_term_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          cronies_term net
    }.
End CroniesTermInterface.
