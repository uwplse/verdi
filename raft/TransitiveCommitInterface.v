Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import Raft.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.
Require Import CommonDefinitions.

Section TransitiveCommit.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition transitive_commit net :=
    forall h e e' t,
      In e (log (snd (nwState net h))) ->
      In e' (log (snd (nwState net h))) ->
      eIndex e <= eIndex e' ->
      committed net e' t ->
      committed net e t.

  Class transitive_commit_interface : Prop :=
    {
      transitive_commit_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          transitive_commit net
    }.
  
End TransitiveCommit.
