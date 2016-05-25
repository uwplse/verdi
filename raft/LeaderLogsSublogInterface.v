Require Import Raft.
Require Import RaftRefinementInterface.

Section LeaderLogsSublogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_sublog (net : network) :=
    forall leader t ll e h,
      type (snd (nwState net leader)) = Leader ->
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In e ll ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).

  Class leaderLogs_sublog_interface : Prop :=
    {
      leaderLogs_sublog_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leaderLogs_sublog net
    }.

End LeaderLogsSublogInterface.
