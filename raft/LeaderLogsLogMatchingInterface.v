Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.

Section LeaderLogsLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_entries_match_host (net : network) : Prop :=
    forall h h' t ll,
      In (t, ll) (leaderLogs (fst (nwState net h'))) ->
      entries_match (log (snd (nwState net h))) ll.

  Class leaderLogs_entries_match_interface : Prop :=
    {
      leaderLogs_entries_match_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leaderLogs_entries_match_host net
    }.
End LeaderLogsLogMatching.
