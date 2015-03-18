Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import AppendEntriesRequestLeaderLogsInterface.

Section AppendEntriesRequestLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem append_entries_leaderLogs_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      append_entries_leaderLogs net.
  Admitted.

  Instance aerlli : append_entries_leaderLogs_interface.
  Admitted.

End AppendEntriesRequestLeaderLogs.
