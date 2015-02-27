Require Import List.
Import ListNotations.

Require Import PeanoNat.

Require Import Util.
Require Import Net.
Require Import Raft.

Section CommonDefinitions.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition entries_match entries entries' :=
    forall e e' e'',
      eIndex e = eIndex e' ->
      eTerm e = eTerm e' ->
      In e entries ->
      In e' entries' ->
      eIndex e'' <= eIndex e ->
      (In e'' entries <-> In e'' entries').

  Fixpoint sorted log :=
    match log with
      | [] => True
      | e :: es =>
        (forall e',
           In e' es ->
           eIndex e > eIndex e' /\ eTerm e >= eTerm e') /\
        sorted es
    end.

  Fixpoint argmax {A : Type} (f : A -> nat) (l : list A) : option A :=
    match l with
      | a :: l' => match argmax f l' with
                     | Some a' => if f a' <=? f a then
                                    Some a
                                  else
                                    Some a'
                     | None => Some a
                   end
      | [] => None
    end.


  Definition applied_entries (sigma : name -> raft_data) : (list entry) :=
    match argmax (fun h => lastApplied (sigma h)) (all_fin N) with
      | Some h =>
        rev (removeAfterIndex (log (sigma h)) (lastApplied (sigma h)))
      | None => []
    end.

    Definition uniqueIndices (xs : list entry) : Prop :=
    NoDup (map eIndex xs).
End CommonDefinitions.