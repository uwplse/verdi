Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition every_entry_was_created (net : network) : Prop :=
    forall e t h l,
      In (t, l) (leaderLogs (fst (nwState net h))) ->
      In e l ->
      exists h ll,
        In (eTerm e, ll) (leaderLogs (fst (nwState net h))).

  Class every_entry_was_created_interface : Prop :=
    {
      every_entry_was_created_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          every_entry_was_created net
    }.
End EveryEntryWasCreated.
