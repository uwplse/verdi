Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
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

  Definition logs_leaderLogs_nw net :=
    forall p t n pli plt es ci e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e es ->
      exists leader ll es' ll',
        In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\
        Prefix ll' ll /\
        removeAfterIndex es (eIndex e) = es' ++ ll' /\
        (forall e', In e' es' -> eTerm e' = eTerm e) /\
        ((plt = eTerm e /\ pli > maxIndex ll)  \/
         (exists e, In e ll /\ eIndex e = pli /\ eTerm e = plt /\ (ll' <> [] \/
                                                             pli = maxIndex ll)) \/
         plt = 0 /\ pli = 0 /\ ll' = ll).

  Class logs_leaderLogs_interface : Prop :=
    {
      logs_leaderLogs_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          logs_leaderLogs net;
      logs_leaderLogs_nw_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          logs_leaderLogs_nw net
    }.
End LogsLeaderLogs.
