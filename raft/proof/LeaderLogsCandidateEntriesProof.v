Require Import List.
Import ListNotations.

Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import RefinementCommonDefinitions.

Require Import LeaderLogsCandidateEntriesInterface.

Section CandidateEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance llcei : leaderLogs_candidate_entries_interface.
  Admitted.
End CandidateEntriesInterface.
