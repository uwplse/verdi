Require Import List.
Import ListNotations.
Require Import NArith.
Require Import PArith.
Require Import String.
Require Import Ascii.

Require Import StructTact.StructTactics.

Require Import Verdi.Coqlib.
Require Export Verdi.Maps.

Module ITree(X: INDEXED_TYPE) <: TREE.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t := PTree.t.
  Definition empty := PTree.empty.
  Definition get {A: Type} (i: X.t) (m: t A) := PTree.get (X.index i) m.
  Definition set {A: Type} (i: X.t) (v: A) (m: t A) := PTree.set (X.index i) v m.
  Definition remove {A: Type} (i: X.t) (m: t A) := PTree.remove (X.index i) m.

  Theorem gempty :
    forall (A: Type) (k: elt), get k (empty A) = None.
  Proof.
    intros. unfold get. apply PTree.gempty.
  Qed.

  Theorem gss :
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros. unfold get, set. apply PTree.gss.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PTree.gso.
    unfold not in *. intros. find_apply_lem_hyp X.index_inj. contradiction.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros. unfold get, set.
    rewrite PTree.gsspec.
    repeat break_if; try find_apply_lem_hyp X.index_inj; congruence.
  Qed.

  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    intros. unfold get. apply PTree.grs.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros. unfold get. apply PTree.gro.
    unfold not in *. intros. find_apply_lem_hyp X.index_inj. contradiction.
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. unfold get, remove. rewrite PTree.grspec.
    repeat break_if; try find_apply_lem_hyp X.index_inj; congruence.
  Qed.
End ITree.

Module IndexedString <: INDEXED_TYPE.
  Definition t := string.
  Definition eq := string_dec.

  Fixpoint positive_of_digits (l : list bool) (p : positive) : positive :=
    match l with
    | [] => p
    | b :: l' => if b then xI (positive_of_digits l' p) else xO (positive_of_digits l' p)
    end.

  Definition list_bool_of_ascii (a : ascii) : list bool :=
    let (a0,a1,a2,a3,a4,a5,a6,a7) := a in
    [a0; a1; a2; a3; a4; a5; a6; a7].

  Fixpoint index (s : string) : positive :=
    match s with
    | EmptyString => 1
    | String a s' => positive_of_digits (list_bool_of_ascii a) (index s')
    end.

  Lemma positive_of_digits_inj :
    forall l l' p p',
      List.length l = List.length l' ->
      positive_of_digits l p = positive_of_digits l' p' ->
      l = l' /\ p = p'.
  Proof.
    induction l; destruct l'; intros; try discriminate; auto.
    simpl in *. do 2 break_match; try discriminate;
      solve [ find_inversion; find_apply_hyp_hyp; break_and; subst; auto ].
  Qed.

  Theorem index_inj :
    forall (x y : t),
      index x = index y ->
      x = y.
  Proof.
    induction x; destruct y; intros.
    - reflexivity.
    - simpl in *. unfold list_bool_of_ascii in *.
      break_let; simpl in * ; repeat break_match; congruence.
    - simpl in *. unfold list_bool_of_ascii in *.
      break_let; simpl in *; repeat break_match; congruence.
    - simpl in *. unfold list_bool_of_ascii in *. repeat break_let.
      find_apply_lem_hyp positive_of_digits_inj.
      + subst. break_and. find_inversion. find_apply_hyp_hyp. subst. reflexivity.
      + reflexivity.
  Qed.
End IndexedString.

Module LogTimeStringMap := ITree(IndexedString).

Module EqString <: EQUALITY_TYPE.
  Definition t := string.
  Definition eq := string_dec.
End EqString.

Module LinearTimeStringMap := ETree(EqString).
