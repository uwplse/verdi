Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.
Require Import CommonDefinitions.

Require Import CommitRecordedCommittedInterface.

Section CommitRecordedCommitted.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem commit_recorded_committed_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      commit_recorded_committed net.
  Admitted.

  Instance crci : commit_recorded_committed_interface.
  Proof.
    split.
    exact commit_recorded_committed_invariant.
  Qed.
End CommitRecordedCommitted.