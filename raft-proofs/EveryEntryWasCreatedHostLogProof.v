Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import LeadersHaveLeaderLogsInterface.
Require Import EveryEntryWasCreatedHostLogInterface.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhlli : leaders_have_leaderLogs_interface}.
  Context {rri : raft_refinement_interface}.

  Instance eewchli : every_entry_was_created_host_log_interface.
  Admitted.
End EveryEntryWasCreated.
