Require Import List.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AllEntriesLeaderLogsInterface.

Section AllEntriesLeaderLogs.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Instance aelli :  all_entries_leader_logs_interface.
  Admitted.
End AllEntriesLeaderLogs.
