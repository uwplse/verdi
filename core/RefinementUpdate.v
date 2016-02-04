Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.
Require Import ExtensionalUpdate.
Import ListNotations.


Section RefinementUpdate.
  Context `{params : SimpleUpdateParams}.

  Variable refinements :
    list (data -> data -> Prop).

  Variable refinements_valid :
    forall n update,
      Nth updates (S n) update ->
      exists refinement,
        Nth refinements n refinement.

  Variable update_establishes_refinement :
    forall n update up failed net h out d ms refinement,
      su_reachable_state (up, failed, net) ->
      up h = n ->
      Nth updates (S n) update ->
      huUpdate update h (nwState net h) = (out, d, ms) ->
      Nth refinements n refinement ->      
      out = nil /\
      ms = nil /\
      refinement (nwState net h) d.

  Definition equiv_mod_host h (st st' : (name -> nat) * list name * network) :=
    (forall h',
        h <> h' ->
        (fst (fst st)) h' = (fst (fst st')) h') /\
    snd (fst st) = snd (fst st') /\
    (forall h',
        h <> h' ->
        nwState (snd st) h' = nwState (snd st') h') /\
    nwPackets (snd st) = nwPackets (snd st').

  Variable input_handlers_preserve_refinements :
    forall n update1 update2 st st' h inp out d ms out' d' ms' refinement,
      su_reachable_state st ->
      su_reachable_state st' ->
      (fst (fst st)) h = n ->
      (fst (fst st')) h = S n ->
      Nth updates n update1 ->
      Nth updates (S n) update2 ->
      Nth refinements n refinement ->
      refinement (nwState (snd st) h) (nwState (snd st') h) ->
      huInput update1 h inp (nwState (snd st) h) = (out, d, ms) ->
      huInput update2 h inp (nwState (snd st') h) = (out', d', ms') ->
      refinement d d' /\ out = out' /\ ms = ms'.

  Variable first_update : handlerUpdate P.
  Variable first_update_first : Nth updates 0 first_update.
  
  
  Definition multi_updates := updates.

  Instance one_update_params : SimpleUpdateParams P :=
    { updates := [first_update] }.

  Notation step_one := (@step_u _ _ _ one_update_params).
  Notation step_multi := (@step_u _ _ _ params).
  Notation step_one_star := (@step_u_star _ _ _ one_update_params).
  Notation step_multi_star := (@step_u_star _ _ _ params).

  Fixpoint refinement_path n ->
  
