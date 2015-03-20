Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section LogsLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition logs_leaderLogs (net : network) : Prop :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      exists leader ll es,
        In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\
        removeAfterIndex (log (snd (nwState net h))) (eIndex e) = es ++ ll /\
        (forall e', In e' es -> eTerm e' = eTerm e).

  Class logs_leaderLogs_interface : Prop :=
    {
      logs_leaderLogs_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          logs_leaderLogs net
    }.
End LogsLeaderLogs.
