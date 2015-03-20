Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import LogsLeaderLogsInterface.

Section LogsLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem logs_leaderLogs_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_leaderLogs net.
  Admitted.

  Instance llli : logs_leaderLogs_interface.
  Proof.
    split. eauto using logs_leaderLogs_invariant.
  Qed.

End LogsLeaderLogs.
