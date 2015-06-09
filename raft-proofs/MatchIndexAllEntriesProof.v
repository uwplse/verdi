Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import MatchIndexAllEntriesInterface.


Section MatchIndexAllEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Instance miaei : match_index_all_entries_interface.
  Admitted.

End MatchIndexAllEntries.  