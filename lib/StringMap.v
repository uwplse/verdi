Require Import List.
Import ListNotations.
Require Import NArith.
Require Import PArith.
Require Import String.

Require Import Coqlib.
Require Import VerdiTactics.
Require Export Maps.

Module ITree(X: INDEXED_TYPE) (*<: TREE*).

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

  (*Definition beq: forall {A: Type}, (A -> A -> bool) -> t A -> t A -> bool := PTree.beq.
  Theorem beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).
  Proof.
  Admitted.

  Definition map: forall (A B: Type), (elt -> A -> B) -> t A -> t B := PTree.map (fun i v => f (X.value i) v) m.
  Hypothesis gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Variable map1:
    forall (A B: Type), (A -> B) -> t A -> t B.
  Hypothesis gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Variable combine:
    forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C.
  Hypothesis gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).

  (** Enumerating the bindings of a tree. *)
  Variable elements:
    forall (A: Type), t A -> list (elt * A).
  Hypothesis elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Hypothesis elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Hypothesis elements_keys_norepet:
    forall (A: Type) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).
  Hypothesis elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Hypothesis elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.

  (** Folding a function over all bindings of a tree. *)
  Variable fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Hypothesis fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  (** Same as [fold], but the function does not receive the [elt] argument. *)
  Variable fold1:
    forall (A B: Type), (B -> A -> B) -> t A -> B -> B.
  Hypothesis fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.*)
End ITree.

Module IndexedString <: INDEXED_TYPE.
  Definition t := string.
  Definition eq := string_dec.

  Fixpoint encode_bools (l : list bool) (p : positive) : positive :=
    match l with
      | nil => p
      | b :: l' => if b then xI (encode_bools l' p) else xO (encode_bools l' p)
    end.
  Fixpoint index (s : string) : positive :=
    match s with
      | EmptyString => 1
      | String a s' => let (a0, a1, a2, a3, a4, a5, a6, a7) := a in
          encode_bools [a0; a1; a2; a3; a4; a5; a6; a7] (index s')
    end.

  Lemma encode_bools_inj :
    forall l l' p p',
      List.length l = List.length l' ->
      encode_bools l p = encode_bools l' p' ->
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
    - simpl in *. repeat break_match; congruence.
    - simpl in *. repeat break_match; congruence.
    - unfold index in *. fold index in *. repeat break_let.
      find_apply_lem_hyp encode_bools_inj.
      + subst. break_and. do 8 (inv H). find_apply_hyp_hyp. subst. reflexivity.
      + reflexivity.
  Qed.
End IndexedString.

Module StringTree := ITree(IndexedString).
Module StringMap := IMap(IndexedString).
