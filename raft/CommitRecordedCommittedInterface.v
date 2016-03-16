Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import GhostSimulations.
Require Import StructTact.Util.
Require Import Raft.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.
Require Import CommonDefinitions.

Section CommitRecordedCommitted.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition commit_recorded_committed net :=
    forall h e,
      commit_recorded (deghost net) h e ->
      committed net e (currentTerm (snd (nwState net h))).

  Class commit_recorded_committed_interface : Prop :=
    {
      commit_recorded_committed_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          commit_recorded_committed net
    }.
  
End CommitRecordedCommitted.
