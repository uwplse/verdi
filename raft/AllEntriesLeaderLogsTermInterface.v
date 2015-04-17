Require Import List.

Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesLeaderLogsTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition allEntries_leaderLogs_term (net : network) : Prop :=
    forall t e h,
      In (t, e) (allEntries (fst (nwState net h))) ->
      t = eTerm e \/
      exists ll leader,
        In (t, ll) (leaderLogs (fst (nwState net leader))) /\
        In e ll.

  Class allEntries_leaderLogs_term_interface : Prop :=
    {
      allEntries_leaderLogs_term_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_leaderLogs_term net
    }.

End AllEntriesLeaderLogsTerm.

