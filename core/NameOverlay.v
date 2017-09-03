Require Import Verdi.Verdi.
Require Import StructTact.Fin.

Require Import OrderedType.

Module Type NameType.
  Parameter name : Type.
  Parameter name_eq_dec : forall x y : name, {x = y} + {x <> y}.
  Parameter nodes : list name.
  Parameter all_names_nodes : forall x, In x nodes.
  Parameter no_dup_nodes : NoDup nodes.
End NameType.

Module Type FinNameType (Import N : NatValue) <: NameType.
  Definition name := fin n.
  Definition name_eq_dec := fin_eq_dec n.
  Parameter nodes : list (fin n).
  Parameter all_names_nodes : forall x, In x nodes.
  Parameter no_dup_nodes : NoDup nodes.
End FinNameType.

Module FinName (Import N : NatValue) <: FinNameType N.
  Definition name := fin n.
  Definition name_eq_dec := fin_eq_dec n.
  Definition nodes := all_fin n.
  Definition all_names_nodes := all_fin_all n.
  Definition no_dup_nodes := all_fin_NoDup n.
End FinName.

Module Type NameOrderedTypeCompat (Import NT : NameType) <: OrderedType.
  Definition t := name.
  Definition eq := @eq name.
  Parameter lt : name -> name -> Prop.
  Definition eq_refl := @eq_refl name.
  Definition eq_sym := @eq_sym name.
  Definition eq_trans := @eq_trans name.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Definition eq_dec := name_eq_dec.
End NameOrderedTypeCompat.

Module FinNameOrderedTypeCompat (N : NatValue) (FN : FinNameType N) <: NameOrderedTypeCompat FN := fin_OT_compat N.

Require Import MSetInterface.

Module Type NameOrderedType (Import NT : NameType) <: OrderedType.
  Definition t := name.
  Definition eq := @eq name.
  Definition eq_equiv := @eq_equivalence name.
  Parameter lt : name -> name -> Prop.
  Parameter lt_strorder : StrictOrder lt.
  Parameter lt_compat : Proper (eq==>eq==>iff) lt.
  Parameter compare : forall x y : name, comparison.
  Parameter compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Definition eq_dec := name_eq_dec.
End NameOrderedType.

Module FinNameOrderedType (N : NatValue) (FN : FinNameType N) <: NameOrderedType FN := fin_OT N.

Module Type AdjacentNameType (Import NT : NameType).
  Parameter adjacent_to : relation name.
  Parameter adjacent_to_dec : forall x y : name, {adjacent_to x y} + {~ adjacent_to x y}.
  Parameter adjacent_to_symmetric : Symmetric adjacent_to.
  Parameter adjacent_to_irreflexive : Irreflexive adjacent_to.
End AdjacentNameType.

Module Type RootNameType (Import NT : NameType).
  Parameter root : name -> Prop.
  Parameter root_dec : forall n, {root n} + {~ root n}.
  Parameter root_unique : forall n n', root n -> root n' -> n = n'.
End RootNameType.

Module FinCompleteAdjacentNameType (Import N : NatValue) (FN : FinNameType N) <: AdjacentNameType FN.
  Inductive fin_complete : fin n -> fin n -> Prop :=
  | fin_complete_neq : forall x y, x <> y -> fin_complete x y.
  
  Definition adjacent_to : relation (fin n) := fin_complete.

  Definition adjacent_to_dec : forall x y, {adjacent_to x y} + { ~ adjacent_to x y}.
    intros x y.
    case (fin_eq_dec n x y); intro H_eq.
    - rewrite H_eq.
      right.
      intros H_r.
      inversion H_r.
      auto.
    - left.
      apply fin_complete_neq.
      auto.
  Defined.

  Lemma adjacent_to_symmetric : Symmetric adjacent_to.
  Proof.
    unfold Symmetric.
    intros x y H_r.
    inversion H_r; subst.
    apply fin_complete_neq.
    intro H_eq.
    rewrite H_eq in H.
    auto.
  Qed.

  Lemma adjacent_to_irreflexive : Irreflexive adjacent_to.
  Proof.
    unfold Irreflexive; unfold Reflexive; unfold complement.
    intros x H_x.
    inversion H_x.
    auto.
  Qed.
End FinCompleteAdjacentNameType.

Module FinRootNameType (Import N : NatValue) (FN : FinNameType N) <: RootNameType FN.
  Definition root (x : fin n) := fin_to_nat x = 0.

  Definition root_dec (x : fin n) := Nat.eq_dec (fin_to_nat x) 0.

  Lemma root_unique : forall x y, root x -> root y -> x = y.
  Proof.
    intros x y.
    unfold root.
    intros H_x H_y.
    case (fin_compare n x y); intro cmp; case cmp; intro H_cmp.
    - inversion H_cmp; auto.
    - inversion H_cmp.
      unfold fin_lt in H.
      rewrite H_x in H.
      rewrite H_y in H.
      contradict H.
      auto with arith.
    - inversion H_cmp.
      unfold fin_lt in H.
      rewrite H_x in H.
      rewrite H_y in H.
      contradict H.
      auto with arith.
  Qed.
End FinRootNameType.
