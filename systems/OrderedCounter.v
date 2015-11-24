Require Import List.
Import ListNotations.

Require Import Arith.
Require Import Omega.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Logic.FunctionalExtensionality.

Set Implicit Arguments.

Section OrderedCounter.
  Inductive Name := Producer | Consumer.
  Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Inductive Msg := Count : nat -> Msg.
  Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
    decide equality.
    apply eq_nat_dec.
  Defined.

  Inductive Input := Request.
  Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
    destruct x,y. auto.
  Defined.

  Inductive Output := Counted : nat -> Output.
  Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
    decide equality.
    apply eq_nat_dec.
  Defined.

  Definition Data := nat.

  Definition init_Data := 0.

  Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

  Definition NetHandler (me : Name) (m : Msg) : Handler Data :=
    match me with
    | Producer => nop
    | Consumer => match m with
                 | Count n => modify (plus n)
                 end
    end.

  Definition InputHandler (me : Name) (i : Input) : Handler Data :=
    match me with
    | Producer => n <- get ;; put (S n) ;; send (Consumer, Count n)
    | Consumer => nop
    end.

  Instance Counter_BaseParams : BaseParams :=
    {
      data := Data;
      input := Input;
      output := Output
    }.

  Definition Nodes : list Name := [Producer; Consumer].

  Lemma all_Names_Nodes : forall n, In n Nodes.
  Proof.
    destruct n; simpl; auto.
  Qed.

  Lemma NoDup_Nodes : NoDup Nodes.
  Proof.
    repeat constructor; simpl; intuition discriminate.
  Qed.

  Instance Counter_MultiParams : MultiParams Counter_BaseParams :=
    {
      name := Name;
      name_eq_dec := Name_eq_dec;
      msg := Msg;
      msg_eq_dec := Msg_eq_dec;
      nodes := Nodes;
      all_names_nodes := all_Names_Nodes;
      no_dup_nodes := NoDup_Nodes;
      init_handlers := fun _ => init_Data;
      net_handlers := fun dst src msg s =>
                        runGenHandler_ignore s (NetHandler dst msg);
      input_handlers := fun nm i s =>
                        runGenHandler_ignore s (InputHandler nm i)
    }.

  Fixpoint sum_list (l : list nat) : nat :=
    match l with
    | [] => 0
    | x :: xs => x + sum_list xs
    end.

  Definition triangular (n : nat) : Prop := exists k, n = sum_list (seq 0 k).

  Definition inv (net : ordered_network) : Prop :=
    exists k n,
      onwState net Producer = k + n /\
      onwState net Consumer = sum_list (seq 0 k) /\
      onwPackets net Consumer Consumer = [] /\
      onwPackets net Producer Consumer = map Count (seq k n).

  Lemma inv_init : inv step_o_init.
  Proof.
    exists 0, 0.
    intuition.
  Qed.

  Lemma update2_diff :
    forall A f x y (v : A) x' y',
      x <> x' \/ y <> y' ->
      update2 f x y v x' y'= f x' y'.
  Proof.
    unfold update2.
    intros.
    break_if; intuition.
  Qed.

  Lemma update2_same :
    forall A f x y (v : A),
      update2 f x y v x y = v.
  Proof.
    unfold update2.
    intros.
    break_if; intuition congruence.
  Qed.

  Lemma collate_nil :
    forall from f,
      collate from f [] = f.
  Proof.
    auto.
  Qed.

  Lemma sum_list_seq_shift :
    forall n a k,
      sum_list (seq (k + a) n) = sum_list (seq a n) + k * n.
  Proof.
    induction n; intros.
    - simpl. omega.
    - cbn [seq sum_list].
      specialize (IHn (S a) k).
      rewrite plus_n_Sm.
      rewrite IHn. ring.
  Qed.

  Lemma seq_shift :
    forall n k a,
      seq (k + a) n = map (plus k) (seq a n).
  Proof.
    induction n; intros.
    - auto.
    - simpl. rewrite plus_n_Sm. rewrite IHn. auto.
  Qed.

  Lemma seq_S_length :
    forall n a,
      seq a (S n) = seq a n ++ [a + n].
  Proof.
    induction n; intros.
    - simpl. rewrite <- plus_n_O. auto.
    - specialize (IHn (S a)).
      simpl in *.
      rewrite <- plus_n_Sm.
      auto using f_equal.
  Qed.

  Lemma seq_lengthen :
    forall k n a,
      seq a (k + n) = seq a n ++ seq (a + n) k.
  Proof.
    induction k; intros.
    - simpl. rewrite app_nil_r. auto.
    - cbn [plus]. rewrite seq_S_length. rewrite IHk.
      rewrite seq_S_length.
      rewrite app_assoc. f_equal. f_equal. omega.
  Qed.

  Lemma sum_list_app :
    forall xs ys,
      sum_list (xs ++ ys) = sum_list xs + sum_list ys.
  Proof.
    intros.
    induction xs; intros; simpl; omega.
  Qed.

  Lemma sum_list_seq_lengthen :
    forall k n a,
      sum_list (seq a (k + n)) = sum_list (seq a n) + sum_list (seq (a + n) k).
  Proof.
    intros.
    rewrite seq_lengthen.
    rewrite sum_list_app.
    auto.
  Qed.

  Lemma inv_step : forall net net' tr, inv net -> step_o net net' tr -> inv net'.
  Proof.
    intros.
    match goal with
    | [ H : step_o _ _ _ |- _ ] => invc H
    end; simpl in *; unfold runGenHandler_ignore in *;
    repeat break_let; subst; find_inversion.
    - unfold NetHandler in *.
      destruct to.
      + monad_unfold. find_inversion.
        unfold inv in *.
        break_exists_exists.
        simpl.
        rewrite update_same.
        rewrite update_diff by discriminate.
        repeat rewrite update2_diff by intuition discriminate.
        auto.
      + destruct m as [i]. monad_unfold. find_inversion.
        rewrite collate_nil.
        unfold inv in *.
        break_exists_name k.
        break_exists_name n.
        break_and.
        destruct from; [|congruence].
        repeat find_rewrite.
        destruct n; [discriminate|].
        exists (S k), n.
        cbn [onwState onwPackets].
        rewrite update_same.
        rewrite update_diff by discriminate.
        rewrite update2_diff by intuition discriminate.
        rewrite update2_same.
        repeat find_rewrite.
        cbn [seq map] in *. find_inversion.
        simpl. unfold Data.
        intuition.
        rewrite sum_list_seq_shift with (k := 1) (a := 0).
        omega.
    - unfold InputHandler in *.
      destruct h.
      + monad_unfold. find_inversion.
        unfold inv in *. cbn [onwState onwPackets collate].
        break_exists_name k.
        break_exists_name n.
        exists k, (S n).
        rewrite update_same.
        rewrite update_diff by discriminate.
        rewrite update2_diff by intuition discriminate.
        rewrite update2_same.
        break_and.
        repeat find_rewrite.
        intuition.
        rewrite seq_lengthen with (k := 1) (n := n).
        rewrite map_app. auto.
      + monad_unfold. find_inversion.
        unfold inv in *.
        break_exists_name k. break_exists_name n.
        exists k, n.
        simpl.
        rewrite update_diff by discriminate.
        rewrite update_same.
        intuition.
  Qed.

  Lemma inv_reachable :
    forall net tr,
      step_o_star step_o_init net tr ->
      inv net.
  Proof.
    intros.
    remember step_o_init as x. revert Heqx.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - apply inv_init.
    - concludes. eauto using inv_step.
  Qed.

  Theorem ordered_counter_correct :
    forall net tr,
      step_o_star step_o_init net tr ->
      triangular (onwState net Consumer).
  Proof.
    intros.
    apply inv_reachable in H.
    unfold inv, triangular in *.
    break_exists_name k. break_exists_name n.
    exists k.
    intuition.
  Qed.
End OrderedCounter.
