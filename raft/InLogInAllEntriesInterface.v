Require Import Raft.
Require Import RaftRefinementInterface.

Section InLogInAllEntries.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition in_log_in_all_entries net :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      exists t,
        In (t, e) (allEntries (fst (nwState net h))).

  Class in_log_in_all_entries_interface : Prop :=
    {
      in_log_in_all_entries_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          in_log_in_all_entries net
    }.
End InLogInAllEntries.
