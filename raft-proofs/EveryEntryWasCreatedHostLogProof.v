Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import LeadersHaveLeaderLogsInterface.
Require Import EveryEntryWasCreatedInterface.
Require Import EveryEntryWasCreatedHostLogInterface.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhlli : leaders_have_leaderLogs_interface}.
  Context {rri : raft_refinement_interface}.
  Context {eewci : every_entry_was_created_interface}.

  
  Instance eewchli : every_entry_was_created_host_log_interface.
  split.
  unfold every_entry_was_created_host_log. intros.
  apply every_entry_was_created_in_any_log_invariant; eauto using in_log.
  Qed.
End EveryEntryWasCreated.
