Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section RequestVoteTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition requestVote_term_sanity (net : network) : Prop :=
    forall t h mi mt p,
      In p (nwPackets net) ->
      pBody p = RequestVote t h mi mt ->
      t <= currentTerm (snd (nwState net (pSrc p))).

  Class requestVote_term_sanity_interface : Prop :=
    {
      requestVote_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          requestVote_term_sanity net
    }.
End RequestVoteTermSanity.
