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
End OU.

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

