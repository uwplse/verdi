Require Import VerdiTactics.
Require Import Net.

Require Import FunctionalExtensionality.

Section OU.
  Context `{params : MultiParams}.

  Lemma update_diff :
    forall A sigma x (v : A) y,
      x <> y ->
      update sigma x v y = sigma y.
  Proof.
    unfold update.
    intros.
    break_if; congruence.
  Qed.

  Lemma update_nop :
    forall A sigma x y,
      update (A:=A) sigma x (sigma x) y = sigma y.
  Proof.
    unfold update.
    intros. break_if; congruence.
  Qed.

  Lemma update_eq :
    forall A sigma x y (v : A),
      x = y ->
      update sigma x v y = v.
  Proof.
    intros. subst.
    unfold update.
    break_if; congruence.
  Qed.

  Lemma update_nop_ext :
    forall A sigma h,
      update (A:=A) sigma h (sigma h) = sigma.
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    apply update_nop.
  Qed.

  Lemma update_fun_comm :
    forall A B (f : A -> B) st y v x,
      f (update st y v x) = update (fun x => f (st x)) y (f v) x.
  Proof.
    intros.
    destruct (name_eq_dec x y); subst; rewrite_update; auto.
  Qed.

  Lemma update_nop_ext' :
    forall A (sigma : name -> A) y v,
      sigma y = v ->
      update sigma y v = sigma.
  Proof.
    intros.
    subst.
    apply update_nop_ext.
  Qed.
End OU.

Ltac update_destruct :=
  match goal with
  | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
  end.

Ltac rewrite_update' H :=
  first [rewrite update_diff in H by congruence |
         rewrite update_eq in H by auto ].

Ltac rewrite_update :=
  repeat match goal with
           | [ H : context [ update _ _ _ _ ] |- _ ] =>
             rewrite_update' H; repeat rewrite_update' H
           | [ |- _ ] => repeat (try rewrite update_diff by congruence;
                                 try rewrite update_eq by auto)
         end.

