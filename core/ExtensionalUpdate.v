Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Omega.
Require Import List.
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
      (forall h i d, huInput update1 h i d = huInput update2 h i d) ->
      (forall h h' m d, huNet update1 h h' m d = huNet update2 h h' m d) ->
      (forall d, huReboot update1 d = huReboot update2 d).
  Variable updates_noop :
    forall i update,
      Nth updates i update ->
      (forall h d, huUpdate update h d = (nil, d, nil)).
  
  Variable first_update : handlerUpdate P.
  Variable first_update_first : Nth updates 0 first_update.

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

  Definition step_one_step_multi :
    forall sto sto' stm tr,
      reachable step_one step_u_init sto ->
      step_one sto sto' tr ->
      equiv_except_handlers sto stm ->
      exists stm',
        equiv_except_handlers sto' stm' /\
        step_multi stm stm' tr.
  Proof.
    intros. invcs H0.
    - destruct stm.
      get_invariant updates_valid_inductive.
      unfold updates_valid in *. simpl in *.
      unfold equiv_except_handlers in *. simpl in *.
      intuition. subst.
      match goal with
        | |- context [(?x = _ /\ ?y = _)] =>
          (exists (up, x, y))
      end.
      intuition.
      destruct n.
      simpl in *. subst. destruct p0. simpl in *. 
      
      exists (up, snd p0, snd ).
      eexists; unfold equiv_except_handlers; simpl; intuition eauto.
      pose proof .
      copy_apply H0 H.

      assert (exists handlers, Nth updates (up (pDst p)) handlers).
      + 
    
  
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
