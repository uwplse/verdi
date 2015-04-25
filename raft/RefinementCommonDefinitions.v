Require Import List.
Import ListNotations.

Require Import PeanoNat.
Require Import Arith.

Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section CommonDefinitions.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition candidateEntries (e : entry) (sigma : name -> _) : Prop :=
    exists h : name,
      wonElection (dedup name_eq_dec (cronies (fst (sigma h)) (eTerm e))) = true /\
      (currentTerm (snd (sigma h)) = eTerm e ->
       type (snd (sigma h)) <> Candidate).
End CommonDefinitions.