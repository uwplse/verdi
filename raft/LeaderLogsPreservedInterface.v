Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section LeaderLogsPreserved.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_preserved (net : network) : Prop :=
    forall h ll t' h' ll' e e',
      In (eTerm e, ll) (leaderLogs (fst (nwState net h))) ->
      In (t', ll') (leaderLogs (fst (nwState net h'))) ->
      In e ll' ->
      In e' ll ->
      In e' ll'.

  Class leaderLogs_preserved_interface : Prop :=
    {
      leaderLogs_preserved_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leaderLogs_preserved net
    }.
End LeaderLogsPreserved.
