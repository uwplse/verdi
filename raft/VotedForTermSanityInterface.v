Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section VotedForTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition votedFor_term_sanity (net : network) : Prop :=
    forall t h h',
      currentTerm (snd (nwState net h')) = t ->
      votedFor (snd (nwState net h')) = Some h ->
      t <= currentTerm (snd (nwState net h)).

  Class votedFor_term_sanity_interface : Prop :=
    {
      votedFor_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          votedFor_term_sanity net
    }.
End VotedForTermSanity.
