Require Import List.

Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import LeaderLogsSublogInterface.

Section LeaderLogsSublog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem leaderLogs_sublog_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_sublog net.
  Admitted.

  Instance llsli : leaderLogs_sublog_interface.
  Proof.
    split.
    exact leaderLogs_sublog_invariant.
  Qed.
End LeaderLogsSublog.
