Require Export OrderedType.
Require Export Structures.OrderedTypeEx.

Require Import Ascii.
Require Import String.
Require Import Omega.

Require Import mathcomp.ssreflect.ssreflect.

Inductive lex_lt: string -> string -> Prop :=
| lex_lt_lt : forall (c1 c2 : ascii) (s1 s2 : string),
  nat_of_ascii c1 < nat_of_ascii c2 ->
  lex_lt (String c1 s1) (String c2 s2)
| lex_lt_eq : forall (c : ascii) (s1 s2 : string),
  lex_lt s1 s2 ->
  lex_lt (String c s1) (String c s2)
| lex_lt_empty : forall (c : ascii) (s : string),
  lex_lt EmptyString (String c s).

Inductive lex_order : string -> string -> Prop :=
| lex_order_empty :
    lex_order EmptyString EmptyString
| lex_order_char_lt :
    forall (c1 c2: ascii) (s1 s2: string),
      nat_of_ascii c1 < nat_of_ascii c2 ->
      lex_order (String c1 s1) (String c2 s2)
| lex_order_char_eq :
  forall (c: ascii) (s1 s2: string),
    lex_order s1 s2 ->
    lex_order (String c s1) (String c s2)
| lex_order_empty_string :
  forall s, lex_order EmptyString s.

Definition lex_le (s1 s2 : string) : Prop := lex_lt s1 s2 \/ s1 = s2.

Lemma lex_le_in_lex_order : forall (s1 s2 : string), lex_order s1 s2 -> lex_le s1 s2.
Proof.
move => s1 s2.
elim {s1 s2}.
- by right.
- move => c1 c2 s1 s2 H_lt.
  left.
  exact: lex_lt_lt.
- move => c s1 s2 H_ord H_le.
  case: H_le => H_le; first by left; exact: lex_lt_eq.
  by rewrite H_le; right.
- case; first by right. 
  move => c s.
  left.
  exact: lex_lt_empty.
Qed.

Lemma lex_order_refl : forall (s : string), lex_order s s.
Proof.
elim; first exact: lex_order_empty_string.
move => a s H_ord.
exact: lex_order_char_eq.
Qed.
  
Lemma lex_order_lex_le : forall (s1 s2 : string), lex_le s1 s2 -> lex_order s1 s2.
move => s1 s2 H_le.
case: H_le => H_le.
  elim: H_le.
  - move => c1 c2 s0 s3 H_lt.
    exact: lex_order_char_lt.
  - move => c s0 s3 H_lt H_ord.
    exact: lex_order_char_eq.
  - move => c s.
    exact: lex_order_empty_string.   
rewrite -H_le.
exact: lex_order_refl.
Qed.

Theorem lex_lt_trans : forall s0 s1 s2, lex_lt s0 s1 -> lex_lt s1 s2 -> lex_lt s0 s2.
Proof.
elim.
- move => s1 s2 H_lt H_lt'.
  inversion H_lt; subst.
  inversion H_lt'; subst; first exact: lex_lt_empty.
  exact: lex_lt_empty.
- move => a s IH s1 s2 H_lt H_lt'.
  inversion H_lt; subst; inversion H_lt'; subst.
  * apply: lex_lt_lt.
    by omega.
  * exact: lex_lt_lt.    
  * exact: lex_lt_lt.
  * apply: lex_lt_eq. 
    exact: IH H3.
Qed.

Theorem lex_lt_not_eq : forall s0 s1, lex_lt s0 s1 -> s0 <> s1.
Proof.
elim.
- move => s0 H_lt.
  by inversion H_lt; subst.
- move => a s IH s1 H_lt.
  inversion H_lt; subst.
    move => H_eq.
    injection H_eq => H_eq' H_eq''.
    rewrite H_eq'' in H2.
    by omega.
  move => H_eq.
  injection H_eq => H_eq'.
  contradict H_eq'.
  exact: IH.
Qed.

Lemma nat_of_ascii_injective:
  forall c1 c2, nat_of_ascii c1 = nat_of_ascii c2 -> c1 = c2.
Proof.
  intros; simpl.
  assert (ascii_of_nat (nat_of_ascii c1) =
          ascii_of_nat (nat_of_ascii c2))
      as Hinvol. auto.
  repeat rewrite ascii_nat_embedding in Hinvol.
  trivial.
Qed.

Fixpoint compare_string_lex (s0 s1 : string) : Compare lex_lt eq s0 s1.
refine
  (match s0 as ss0, s1 as ss1 return (s0 = ss0 -> s1 = ss1 -> _) with 
   | EmptyString, EmptyString => fun H_eq H_eq' => EQ _
   | EmptyString, String c' s'1 => fun H_eq H_eq' => LT _
   | String c s'0, EmptyString => fun H_eq H_eq' => GT _
   | String c s'0, String c' s'1 => fun H_eq H_eq' => 
     match lt_eq_lt_dec (nat_of_ascii c) (nat_of_ascii c') with
     | inleft (left H_dec) => LT _
     | inleft (right H_dec) => 
       match compare_string_lex s'0 s'1 with
       | LT H_lt => LT _
       | EQ H_eq_lex => EQ _
       | GT H_gt => GT _
       end
     | inright H_dec => GT _
     end
   end (refl_equal _) (refl_equal _)); rewrite H_eq H_eq' //.
- exact: lex_lt_empty.
- exact: lex_lt_empty.
- exact: lex_lt_lt.
- apply nat_of_ascii_injective in H_dec.
  rewrite H_dec.
  exact: lex_lt_eq.
- apply nat_of_ascii_injective in H_dec.
  by rewrite H_dec H_eq_lex.
- apply nat_of_ascii_injective in H_dec.
  rewrite H_dec.
  exact: lex_lt_eq.
- exact: lex_lt_lt.
Defined.

Module string_as_OT : OrderedType
    with Definition t := string
    with Definition eq := @eq string.
Definition t := string.
Definition eq := @eq string.
Definition lt := lex_lt.
Definition eq_refl := @eq_refl string.
Definition eq_sym := @eq_sym string.
Definition eq_trans := @eq_trans string.
Definition lt_trans := lex_lt_trans.
Definition lt_not_eq := lex_lt_not_eq.
Definition compare := compare_string_lex.
Definition eq_dec := string_dec.
End string_as_OT.
