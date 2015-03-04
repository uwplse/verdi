Require Import List.
Import ListNotations.

Require Import PeanoNat.
Require Import Arith.

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

    Fixpoint execute_log' (log : list entry) (st : data) (l : list (input * output))
    : (list (input * output) * data) :=
      match log with
        | [] => (l, st)
        | e :: log' => let '(o, st') := handler (eInput e) st in
                       execute_log' log' st' (l ++ [(eInput e, o)])
      end.

    Definition execute_log (log : list entry) : (list (input * output) * data) :=
      execute_log' log init [].

    Definition key : Type := nat * nat.

    Definition key_eq_dec : forall x y : key, {x = y} + {x <> y}.
    Proof.
      decide equality; auto using eq_nat_dec.
    Qed.

    Definition key_of (e : entry) :=
      (eClient e, eId e).

    Fixpoint deduplicate_log' (log : list entry) (ks : list key) : list entry :=
      match log with
        | [] => []
        | e :: es => if (@in_dec key key_eq_dec (key_of e) ks) then
                       deduplicate_log' es ks
                     else
                       e :: deduplicate_log' es ((key_of e) :: ks)
      end.

    Definition deduplicate_log l := deduplicate_log' l [].
End CommonDefinitions.