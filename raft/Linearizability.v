Require Import List.
Import ListNotations.

Require Import Util.
Require Import VerdiTactics.

Section Linearizability.
  Variable K : Type.
  Variable K_eq_dec : forall x y : K, {x = y} + {x <> y}.

  Inductive op : Type :=
  | I : K -> op
  | O : K -> op.

  Definition op_eq_dec :
    forall x y : op, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  Inductive IR : Type :=
  | IRI : K -> IR
  | IRO : K -> IR
  | IRU : K -> IR.

  Definition IR_eq_dec :
    forall x y : IR, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  
  (* Hypothesis trace_NoDup : NoDup trace. *)
  (* also maybe: no Us *)
  (* alse maybe: every O has corresponding I before it *)

  Definition acknowledged_op (k : K) (trace : list op) :=
    In (O k) trace.

  Inductive acknowledge_all_ops : list op ->  list IR -> Prop :=
  | AAO_nil : acknowledge_all_ops [] []
  | AAO_IU : forall k tr out,
               ~ acknowledged_op k tr ->
               acknowledge_all_ops tr out ->
               acknowledge_all_ops (I k :: tr) (IRI k :: IRU k :: out)
  | AAO_I_dorp : forall k tr out,
                   ~ acknowledged_op k tr ->
                   acknowledge_all_ops tr out ->
                   acknowledge_all_ops (I k :: tr) out
  | AAO_IO : forall k tr out,
               acknowledged_op k tr ->
               acknowledge_all_ops tr out ->
               acknowledge_all_ops (I k :: tr) (IRI k :: out)
  | AAO_O : forall k tr out,
              acknowledge_all_ops tr out ->
              acknowledge_all_ops (O k :: tr) (IRO k :: out).

  Definition good_move (x y : IR) : Prop :=
    (forall k, x <> IRO k /\ y <> IRI k).

  Inductive IR_equivalent : list IR -> list IR -> Prop :=
  | equiv_nil : IR_equivalent [] []
  | equiv_cons : forall x xs ys,
                   IR_equivalent xs ys ->
                   IR_equivalent (x :: xs) (x :: ys)
  | equiv_move : forall x y xs ys,
                   IR_equivalent xs ys ->
                   good_move x y ->
                   IR_equivalent (x :: y :: xs) (y :: x :: ys)
  | equiv_trans : forall l1 l2 l3,
                    IR_equivalent l1 l2 ->
                    IR_equivalent l2 l3 ->
                    IR_equivalent l1 l3.

  Fixpoint good_trace (l : list IR) : Prop :=
    match l with
      | [] => True
      | IRI k :: IRO k' :: l' => k = k' /\ good_trace l'
      | IRI k :: IRU k' :: l' => k = k' /\ good_trace l'
      | _ => False
    end.

  Definition equivalent (l : list op) (ir : list IR) : Prop :=
    exists ir',
      acknowledge_all_ops l ir' /\
      IR_equivalent ir' ir /\
      good_trace ir.

  Functional Scheme good_trace_ind := Induction for  good_trace Sort Prop.

  Theorem equivalent_intro :
    forall l ir,
      good_trace ir ->
      (forall k, In (O k) l -> In (IRO k) ir) ->
      (forall k, In (IRO k) ir -> In (O k) l) ->
      (forall k k', In (I k') l -> before op_eq_dec (O k) (I k') l ->
               before IR_eq_dec (IRO k) (IRI k') ir) ->
      equivalent l ir.
  Proof.
  Admitted.

(*
  Lemma good_trace_acknowledge_all_ops_id :
    forall l,
      good_trace l ->
      exists l',
        acknowledge_all_ops l l' /\
        export l' = l.
  Proof.
    intros l H.
    functional induction (good_trace l); intuition.
    - exists nil. intuition. constructor.
    - break_exists. break_and. subst.
      exists (IRI k' :: IRO k' :: x). intuition.
      apply AAO_IO.
      + constructor. auto.
      + apply AAO_O. auto.
  Qed.

  Lemma IR_equivalent_refl :
    forall l,
      IR_equivalent l l.
  Proof.
    induction l.
    - constructor.
    - constructor. auto.
  Qed.

  Lemma good_trace_equiv :
    forall l,
      good_trace l ->
      equivalent l l.
  Proof.
    unfold equivalent.
    intros.
    find_copy_apply_lem_hyp good_trace_acknowledge_all_ops_id.
    break_exists. break_and.
    subst.
    exists x.
    intuition.
    exists x.
    intuition auto using IR_equivalent_refl.
  Qed.

*)

End Linearizability.
