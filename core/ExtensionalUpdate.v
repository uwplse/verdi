Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.
Import ListNotations.

Section SimpleUpdateFacts.
  Context `{params : SimpleUpdateParams}.

  Definition su_reachable_state st :=
    exists tr,
      step_u_star step_u_init st tr.

  Definition updates_valid (st : (name -> nat) * list name * network) :=
    forall h,
      (fst (fst st)) h = 0 \/ (fst (fst st)) h < length updates.
  
  Lemma Nth_lt_length :
    forall A l (x : A) i,
      Nth l i x ->
      i < length l.
  Proof.
    intros. induction H; simpl; omega.
  Qed.

  Lemma updates_valid_inductive :
    inductive_invariant step_u step_u_init updates_valid.
  Proof.
    unfold inductive_invariant. split.
    - unfold updates_valid, step_u_init. intuition.
    - unfold inductive. intros.
      inversion H0; subst; intuition.
      find_apply_lem_hyp Nth_lt_length.
      unfold updates_valid.
      intros.
      simpl. break_if; intuition.
  Qed.

End SimpleUpdateFacts.

Section ExtensionalUpdate.
  Context `{params : SimpleUpdateParams}.
  
  Variable inv : network -> list (name * (input + list output)) -> Prop.

  Definition inv_holds_multi :=
    forall st' tr,
      step_u_star step_u_init st' tr ->
      inv (snd st') tr.

  Variable all_handlers_ext_equal :
    forall i1 i2 update1 update2,
      Nth updates i1 update1 ->
      Nth updates i2 update2 ->
      (forall h i d, huInput update1 h i d = huInput update2 h i d) /\
      (forall h h' m d, huNet update1 h h' m d = huNet update2 h h' m d) /\
      (forall d, huReboot update1 d = huReboot update2 d).
  Variable updates_noop :
    forall i update,
      Nth updates i update ->
      (forall h d, huUpdate update h d = (nil, d, nil)).
  
  Variable first_update : handlerUpdate P.
  Variable first_update_first : Nth updates 0 first_update.

  Definition multi_updates := updates.

  Instance one_update_params : SimpleUpdateParams P :=
    { updates := [first_update] }.

  Notation step_one := (@step_u _ _ _ one_update_params).
  Notation step_multi := (@step_u _ _ _ params).

  Ltac get_invariant inv :=
    match goal with
      | H : context [reachable] |- _ =>
        copy_apply (inductive_invariant_true_in_reachable inv) H
    end.

  Definition equiv_except_handlers (st st' : ((name -> nat) * list name * network)) :=
    snd (fst st) = snd (fst st') /\
    snd st = snd st'.

  Lemma Nth_nth :
    forall A (l : list A) n x y,
      Nth l n x ->
      nth n l y = x.
  Proof.
    induction 1; intuition.
  Qed.

  Lemma nth_Nth :
    forall A n (l : list A) y,
      n < length l ->
      Nth l n (nth n l y).
  Proof.
    induction n; intros; destruct l; subst; simpl in *;
    try omega; constructor; intuition.
  Qed.

  Lemma Nth_singleton :
    forall A (x : A) y n,
      Nth [x] n y ->
      y = x.
  Proof.
    intros. inversion H; intuition. solve_by_inversion.
  Qed.
  
  Definition step_one_step_multi :
    forall sto sto' stm tr,
      reachable step_one step_u_init sto ->
      reachable step_multi step_u_init stm ->
      step_one sto sto' tr ->
      equiv_except_handlers sto stm ->
      exists stm',
        equiv_except_handlers sto' stm' /\
        step_multi stm stm' tr.
  Proof.
    intros. invcs H1.
    - destruct stm.
      destruct p0.
      copy_apply (inductive_invariant_true_in_reachable (@updates_valid_inductive _ _ _ params)) H0.
      unfold updates_valid in *. simpl in *.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (n0, x, y))
      end.
      intuition.
      assert (Nth multi_updates (n0 (pDst p))
                  (nth (n0 (pDst p)) multi_updates first_update))
      by
        (match goal with
           | H : forall _, _ \/ _ |- _ =>
             specialize (H (pDst p))
         end; intuition; eauto using nth_Nth;
         repeat find_rewrite;
         erewrite Nth_nth; eauto).
      eapply SU_deliver with (handlers0 := nth (n0 (pDst p)) multi_updates first_update);
        simpl in *; eauto; unfold multi_updates in *.
      find_apply_lem_hyp Nth_singleton. subst.
      find_reverse_rewrite.
      eapply all_handlers_ext_equal; eauto.
    - destruct stm. destruct p.
      copy_apply (inductive_invariant_true_in_reachable (@updates_valid_inductive _ _ _ params)) H0.
      unfold updates_valid in *. simpl in *.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (n0, x, y))
      end.
      intuition.
      assert (Nth multi_updates (n0 h)
                  (nth (n0 h) multi_updates first_update))
      by
        (match goal with
           | H : forall _, _ \/ _ |- _ =>
             specialize (H h)
         end; intuition; eauto using nth_Nth;
         repeat find_rewrite;
         erewrite Nth_nth; eauto).
      eapply SU_input with (handlers0 := nth (n0 h) multi_updates first_update);
        simpl in *; eauto; unfold multi_updates in *.
      find_apply_lem_hyp Nth_singleton. subst.
      find_reverse_rewrite.
      eapply all_handlers_ext_equal; eauto.
    - destruct stm. destruct p0.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (n0, x, y))
      end.
      intuition.
      solve [econstructor; eauto].
    - destruct stm. destruct p0.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (n0, x, y))
      end.
      intuition.
      solve [econstructor; eauto].
    - destruct stm. destruct p.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (n0, x, y))
      end.
      intuition.
      solve [econstructor; eauto].
    - destruct stm. destruct p.
      copy_apply (inductive_invariant_true_in_reachable (@updates_valid_inductive _ _ _ params)) H0.
      unfold updates_valid in *. simpl in *.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (n0, x, y))
      end.
      intuition.
      assert (Nth multi_updates (n0 h)
                  (nth (n0 h) multi_updates first_update))
      by
        (match goal with
           | H : forall _, _ \/ _ |- _ =>
             specialize (H h)
         end; intuition; eauto using nth_Nth;
         repeat find_rewrite;
         erewrite Nth_nth; eauto).
      eapply SU_reboot with (handlers0 := nth (n0 h) multi_updates first_update);
        simpl in *; eauto; unfold multi_updates in *.
      find_apply_lem_hyp Nth_singleton. subst.
      copy_eapply_prop_hyp huReboot @Nth; [|apply first_update_first].
      intuition.
      f_equal. apply functional_extensionality.
      intros.
      find_higher_order_rewrite. auto.
    - match goal with
        | H : Nth _ _ _ |- _ =>
          inversion H
      end. solve_by_inversion.
  Qed.

      
  Definition inv_holds_one :=
    forall st' tr,
      @step_u_star _ _ _ one_update_params step_u_init st' tr ->
      inv st' tr.

  Lemma inv_holds_multi_inv_holds_one :
    inv_holds_multi -> inv_holds_one.
  Proof.
    intro IHM.
    unfold inv_holds_multi, inv_holds_one in *.
    intros.
    intros. induction H.
    - apply IHM. constructor.
    -
      
End ExtensionalUpdate.
