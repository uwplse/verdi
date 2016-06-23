Require Import List.
Import ListNotations.

Require Import Relations.

Require Import Permutation.

Require Import StructTact.StructTactics.
Require Import Net.

Section dup_drop_reorder.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Inductive dup_drop_step : list A -> list A -> Prop :=
  | DDS_dup : forall l p,
      In p l ->
      dup_drop_step l (p :: l)
  | DDS_drop : forall xs p ys,
      dup_drop_step (xs ++ p :: ys) (xs ++ ys).

  Definition dup_drop_step_star := clos_refl_trans_n1 _ dup_drop_step.

  Lemma dup_drop_step_star_trans :
    forall l l' l'',
      dup_drop_step_star l l' ->
      dup_drop_step_star l' l'' ->
      dup_drop_step_star l l''.
  Proof.
    intros.
    apply clos_rt_rtn1_iff.
    eapply rt_trans; apply clos_rt_rtn1_iff; eauto.
  Qed.

  Lemma dup_drop_step_star_step_n1 :
    forall l l' l'',
      dup_drop_step_star l l' ->
      dup_drop_step l' l'' ->
      dup_drop_step_star l l''.
  Proof.
    intros.
    econstructor; eauto.
  Qed.

  Lemma dup_drop_step_star_step_1n :
    forall l l' l'',
      dup_drop_step l l' ->
      dup_drop_step_star l' l'' ->
      dup_drop_step_star l l''.
  Proof.
    intros.
    apply clos_rt_rtn1_iff.
    apply clos_rt_rt1n_iff.
    econstructor; [eauto|].
    apply clos_rt_rt1n_iff.
    apply clos_rt_rtn1_iff.
    auto.
  Qed.

  Lemma dup_drop_step_star_step_1 :
    forall l l',
      dup_drop_step l l' ->
      dup_drop_step_star l l'.
  Proof.
    intros.
    eapply dup_drop_step_star_step_1n; eauto.
    constructor.
  Qed.

  Lemma dup_drop_swap :
    forall l x y,
      dup_drop_step_star (x :: y :: l) (y :: x :: l).
  Proof.
    intros.
    eapply dup_drop_step_star_step_1n; [eapply DDS_dup with (p := y); simpl; auto|].
    eapply dup_drop_step_star_step_1n.
    eapply DDS_drop with (xs := [y; x]) (p := y) (ys := l).
    constructor.
  Qed.

  Lemma dup_drop_cons :
    forall l l' x,
      dup_drop_step_star l l' ->
      dup_drop_step_star (x :: l) (x :: l').
  Proof.
    induction 1.
    - constructor.
    - invc H.
      + eapply dup_drop_step_star_trans; [eauto|].
        eapply dup_drop_step_star_step_1n; [eapply DDS_dup with (p := p); simpl; auto|].
        auto using dup_drop_swap.
      + eapply dup_drop_step_star_trans; [eauto|].
        eapply dup_drop_step_star_step_1n.
        eapply DDS_drop with (xs := x :: xs) (p := p) (ys := ys).
        constructor.
  Qed.

  Lemma dup_drop_Permutation :
    forall l l',
      Permutation l l' ->
      dup_drop_step_star l l'.
  Proof.
    induction 1.
    - constructor.
    - auto using dup_drop_cons.
    - auto using dup_drop_swap.
    - eauto using dup_drop_step_star_trans.
  Qed.

  Lemma remove_not_in_nop :
    forall a l,
      ~ In a l ->
      remove A_eq_dec a l = l.
  Proof.
    induction l; simpl; intuition.
    break_if; congruence.
  Qed.

  Lemma dup_drop_in :
    forall l l' a,
      dup_drop_step_star l l' ->
      In a l' ->
      In a l.
  Proof.
    induction 1; intros.
    - auto.
    - invc H.
      + simpl in *. intuition.
        subst. auto.
      + apply IHclos_refl_trans_n1.
        find_apply_lem_hyp in_app_or.
        intuition.
  Qed.

  Lemma dup_drop_dup_early :
    forall l l' a,
      dup_drop_step_star l l' ->
      In a l ->
      dup_drop_step_star l (a :: l').
  Proof.
    induction 1; intros.
    - apply dup_drop_step_star_step_1. constructor. auto.
    - concludes.
      eapply dup_drop_step_star_trans; eauto.
      apply dup_drop_cons.
      apply dup_drop_step_star_step_1.
      auto.
  Qed.

  Lemma dup_drop_step_star_remove_In :
    forall l' l a,
      In a l' ->
      dup_drop_step_star l (remove A_eq_dec a l') ->
      dup_drop_step_star (a :: l) l'.
  Proof.
    induction l'; simpl; intuition.
    - subst. break_if; try congruence.
      destruct (in_dec A_eq_dec a0 l').
      + find_apply_hyp_hyp.
        eapply dup_drop_step_star_trans; eauto.
        eapply dup_drop_step_star_step_1.
        apply DDS_dup; auto.
      + rewrite remove_not_in_nop in * by auto.
        apply dup_drop_cons. auto.
    - break_if.
      + subst.
        find_apply_hyp_hyp.
        eapply dup_drop_step_star_trans; eauto.
        eapply dup_drop_step_star_step_1.
        apply DDS_dup; auto.
      + pose proof dup_drop_in l _ a ltac:(eauto).
        concludes.
        eapply dup_drop_step_star_step_n1 in H0; [| eapply DDS_drop with (xs := [])].
        simpl in *.
        apply IHl' in H0; auto.
        apply dup_drop_dup_early; auto.
        simpl. intuition.
  Qed.

  Lemma remove_In_elim :
    forall x a l,
      In x (remove A_eq_dec a l) ->
      x <> a /\ In x l.
  Proof.
    induction l; simpl; intuition; break_if; subst; simpl in *; intuition.
  Qed.

  Lemma dup_drop_reorder :
    forall l l' : list A,
      (forall x, In x l' -> In x l) ->
      dup_drop_step_star l l'.
  Proof.
    induction l; intros.
    - destruct l'.
      + constructor.
      + simpl in *. exfalso. eauto.
    - destruct (in_dec A_eq_dec a l').
      + eapply dup_drop_step_star_remove_In. auto.
        apply IHl.
        intros.
        find_apply_lem_hyp remove_In_elim.
        intuition.
        find_apply_hyp_hyp.
        simpl in *. intuition.
        exfalso. eauto.
      + eapply dup_drop_step_star_step_1n.
        eapply DDS_drop with (xs := []).
        apply IHl.
        simpl in *. intros.
        find_copy_apply_hyp_hyp.
        intuition.
        subst. exfalso. eauto.
  Qed.
End dup_drop_reorder.

Section step_f_dup_drop_step.
  Context `{params : FailureParams}.

  Theorem step_f_dup_drop_step :
    forall ps ps' Sigma f,
      dup_drop_step_star _ ps ps' ->
      step_f_star (f, mkNetwork ps Sigma) (f, mkNetwork ps' Sigma) [].
  Proof.
    induction 1.
    - constructor.
    - match goal with
      | [ H : dup_drop_step _ _ _ |- _ ] => invc H
      end.
      + find_apply_lem_hyp in_split. break_exists. break_and. subst.
        apply refl_trans_n1_1n_trace.
        eapply RTn1TStep with (cs := []).
        * apply refl_trans_1n_n1_trace.
          apply IHclos_refl_trans_n1.
        * eapply SF_dup; [simpl; eauto|]. auto.
      + apply refl_trans_n1_1n_trace.
        eapply RTn1TStep with (cs := []).
        * apply refl_trans_1n_n1_trace.
          apply IHclos_refl_trans_n1.
        * eapply SF_drop; [simpl; eauto|]. auto.
  Qed.
End step_f_dup_drop_step.
