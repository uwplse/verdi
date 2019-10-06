Require Import ZArith.

Require Import FMapInterface.
Require Import FMapPositive.
Require Import FMapList.
Require Import FMapFacts.

Require Import String.
Require Import Ascii.
Require Import List.

Require Import StructTact.StructTactics.
Require Import StructTact.StringOrders.

Import ListNotations.

Set Implicit Arguments.

Module Type VWS.
  Declare Module E : DecidableType.

  Definition key := E.t.
  Hint Transparent key : core.

  Parameter t : Type -> Type.

  Section Types.
    Variable elt:Type.

    Parameter empty : t elt.
    Parameter add : key -> elt -> t elt -> t elt.
    Parameter find : key -> t elt -> option elt.
    Parameter remove : key -> t elt -> t elt.

    Parameter empty_o : forall x, find x empty = None.
    Parameter add_eq_o : forall m x y e, E.eq x y -> find y (add x e m) = Some e.
    Parameter add_neq_o : forall m x y e, ~ E.eq x y -> find y (add x e m) = find y m.
    Parameter remove_eq_o : forall m x y, E.eq x y -> find y (remove x m) = None.
    Parameter remove_neq_o : forall m x y, ~ E.eq x y -> find y (remove x m) = find y m.
  End Types.
End VWS.

Module WS_to_VWS (Map : WS) <: VWS.
  Module E := Map.E.
  Module F := Facts Map.
  Definition key := E.t.
  Definition t := Map.t.
  Definition empty := Map.empty.
  Definition add := Map.add.
  Definition find := Map.find.
  Definition remove := Map.remove.
  Definition empty_o := F.empty_o.
  Definition add_eq_o := F.add_eq_o.
  Definition add_neq_o := F.add_neq_o.
  Definition remove_eq_o := F.remove_eq_o.
  Definition remove_neq_o := F.remove_neq_o.
End WS_to_VWS.

Module StringMapList := FMapList.Make string_lex_as_OT_compat.
Module LinearTimeStringMap <: VWS := WS_to_VWS StringMapList.

Module Type IndexedType.
  Parameter t: Type.
  Parameter index: t -> positive.
  Parameter index_inj: forall (x y: t), index x = index y -> x = y.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
End IndexedType.

Module IT_to_DT (I : IndexedType) <: DecidableType.
  Definition t := I.t.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := I.eq.
End IT_to_DT.

Module IndexedPositiveMap (X : IndexedType) <: VWS.
  Module E := IT_to_DT X.
  Module M := PositiveMap.
  Module F := Facts M.

  Definition key := X.t.

  Definition t := M.t.

  Definition empty := M.empty.

  Definition add (A : Type) (i : key) (v : A) (m : t A) : t A :=
    M.add (X.index i) v m.

  Definition find (A : Type) (i : key) (m : t A) : option A :=
    M.find (X.index i) m.

  Definition remove (A : Type) (i : key) (m : t A) : t A :=
    M.remove (X.index i) m.

  Lemma empty_o : forall A x, find x (empty A) = None.
  Proof.
   intros.
   unfold find.
   apply F.empty_o.
  Qed.
    
  Lemma add_eq_o : forall A m x y e, E.eq x y -> @find A y (add x e m) = Some e.
  Proof.
    intros.
    unfold find.
    apply F.add_eq_o.
    rewrite H.
    reflexivity.
   Qed.

  Lemma add_neq_o : forall A m x y e, ~ E.eq x y -> find y (add x e m) = @find A y m.
  Proof.
    intros.
    unfold find.
    apply F.add_neq_o.
    intro H_eq.
    contradict H.
    apply X.index_inj in H_eq.
    assumption.
  Qed.

  Lemma remove_eq_o : forall A m x y, E.eq x y -> @find A y (remove x m) = None.
  Proof.
    intros.
    unfold find.
    apply F.remove_eq_o.
    rewrite H.
    reflexivity.
  Qed.

  Lemma remove_neq_o : forall A m x y, ~ E.eq x y -> find y (remove x m) = @find A y m.
  Proof.
    intros.
    unfold find.
    apply F.remove_neq_o.
    intro H_eq.
    contradict H.
    apply X.index_inj in H_eq.
    assumption.
  Qed.
End IndexedPositiveMap.

Module IndexedString <: IndexedType.
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

Module LogTimeStringMap <: VWS := IndexedPositiveMap IndexedString.
