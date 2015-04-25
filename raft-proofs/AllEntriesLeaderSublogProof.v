Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import AllEntriesLeaderSublogInterface.

Section AllEntriesLeaderSublog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance aelsi : allEntries_leader_sublog_interface.
  Admitted.
End AllEntriesLeaderSublog.
