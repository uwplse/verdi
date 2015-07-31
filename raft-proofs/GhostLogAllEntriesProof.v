Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import RaftMsgRefinementInterface.

Require Import InLogInAllEntriesInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import GhostLogAllEntriesInterface.

Section GhostLogAllEntriesProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rmri : raft_msg_refinement_interface}.
  Context {iliaei : in_log_in_all_entries_interface}.
  
  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).
  
  Instance glaei : ghost_log_allEntries_interface.
  Proof.
  Admitted.
End GhostLogAllEntriesProof.
