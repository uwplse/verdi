Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section AppendEntriesRequestLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition Prefix_sane (l l' : list entry) i :=
    l <> [] \/ i = maxIndex l'.

  Definition append_entries_leaderLogs (net : network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      exists h ll es' ll',
        es = es' ++ ll' /\
        (forall e, In e es' -> eTerm e = t) /\
        In (t, ll) (leaderLogs (fst (nwState net h))) /\
        Prefix ll' ll /\
        ((plt = t /\ pli > maxIndex ll)  \/
         (exists e, In e ll /\ eIndex e = pli /\ eTerm e = plt /\ Prefix_sane ll' ll pli) \/
         plt = 0 /\ pli = 0 /\ ll' = ll).


  Class append_entries_leaderLogs_interface : Prop :=
    {
      append_entries_leaderLogs_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          append_entries_leaderLogs net
    }.
End AppendEntriesRequestLeaderLogs.
