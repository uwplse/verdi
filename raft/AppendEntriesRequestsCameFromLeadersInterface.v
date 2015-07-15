Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section AppendEntriesRequestsCameFromLeaders.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition append_entries_came_from_leaders (net : network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      exists ll,
        In (t, ll) (leaderLogs (fst (nwState net (pSrc p)))).

  Class append_entries_came_from_leaders_interface : Prop :=
    {
      append_entries_came_from_leaders_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          append_entries_came_from_leaders net
    }.
End AppendEntriesRequestsCameFromLeaders.
