Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinement.

Require Import CommonTheorems.


Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section CroniesTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition cronies_term (net : network) :=
    forall h h' t,
      In h (cronies (fst (nwState net h')) t) ->
      t <= currentTerm (snd (nwState net h')).

  Theorem cronies_term_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      cronies_term net.
  Admitted.
End CroniesTerm.