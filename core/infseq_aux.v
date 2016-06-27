Require Import infseq.

Require Import Classical.

Require Import StructTact.StructTactics.
Require Import mathcomp.ssreflect.ssreflect.

Section Aux.

Variable T : Type.

Lemma P_or_not_tl : forall (P : infseq T -> Prop) (s : infseq T),
  P s \/ (~_ P) s.
Proof.
move => P s.
exact: classic.
Qed.

Lemma not_tl_not : forall (P : infseq T -> Prop) (s : infseq T),
  (~_ P) s -> ~ P s.
Proof.
move => P; case => e s.
by move => H_not H_p.
Qed.

Lemma not_eventually_not_always : forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually (~_ P) s ->
  always P s.
Proof.
move => P.
cofix c.
case => e s H_al.
apply: Always.
  case (P_or_not_tl P (Cons e s)) => H_or //.
  by apply (E0 _ (~_ P)) in H_or.
apply: c.
move => /= H_ev.
case: H_al.
exact: E_next.
Qed.

Lemma continuously_both : forall (P Q : infseq T -> Prop) (s : infseq T),
  continuously P s ->
  continuously Q s ->
  continuously (P /\_ Q) s.
Proof.
move => P Q s.
elim => {s}.
  move => s H_al H_ev.
  elim: H_ev H_al => {s}.
    move => s H_al H_al'.
    apply: E0.
    move: s H_al H_al'.
    cofix c.
    case => T5 s H_al H_al'.
    inversion H_al; subst.
    inversion H_al'; subst.
    apply Always; first by split.
    exact: c.
  move => e s H_ev IH H_al.
  apply: E_next.
  apply IH.
  by inversion H_al.  
move => e s H_al IH H_ev.
apply E_next.
apply: IH.
inversion H_ev; subst => //.
inversion H; subst.
exact: E0.
Qed.

Lemma not_always_eventually_not : forall (P : infseq T -> Prop) (s : infseq T),
  ~ (always P s) ->
  eventually (~_ P) s.
Proof.
move => P s H_al.
set Q := eventually _.
case (P_or_not_tl Q s) => //.
rewrite /Q {Q} => H_not.
apply not_tl_not in H_not.
by apply not_eventually_not_always in H_not.
Qed.

Lemma not_eventually_then_always_not : forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually P s ->
  always (~_ P) s.
Proof.
move => P.
cofix c.
case => e s H_al.
apply: Always.
  case (P_or_not_tl P (Cons e s)) => H_or //.
  by apply (E0 _ P) in H_or.
apply: c.
move => /= H_ev.
case: H_al.
exact: E_next.
Qed.

Lemma not_inf_often_then_continuously_not : forall (P : infseq T -> Prop) (s : infseq T),
  ~ (inf_often P s) -> continuously (~_ P) s.
Proof.
move => P s H_al.
apply not_always_eventually_not in H_al.
elim: H_al => {s}.
  move => s H_not.
  apply not_tl_not in H_not.
  apply not_eventually_then_always_not in H_not.
  exact: E0.
move => e s H_ev H_ev'.
exact: E_next.
Qed.

Lemma eventually_always_not_then_not_always_eventually : forall (P : infseq T -> Prop) (s : infseq T),
  continuously (~_ P) s ->
  ~ (inf_often P s).
Proof.
move => P s.
elim => {s}.
  case => T5 s H_al H_al'.
  inversion H_al'; subst.
  elim: H H_al.
    move => s0 H_P H_al.
    by inversion H_al.    
  move => e s0 H_ev H_al H_al''.
  by inversion H_al''.
move => e s H_al H_al' H_al''.
by inversion H_al''.
Qed.

Lemma and_tl_comm : forall (P Q : infseq T -> Prop) (s : infseq T),
  (P /\_ Q) s ->
  (Q /\_ P) s.
Proof.
move => P Q s.
unfold and_tl.
move => H_and.
by break_and.
Qed.

Lemma and_tl_assoc_l : forall (P Q R : infseq T -> Prop) (s : infseq T),
  ((P /\_ Q) /\_ R) s ->
  (P /\_ Q /\_ R) s.
Proof.
move => P Q R s.
unfold and_tl.
move => H_and.
by break_and.
Qed.

Lemma and_tl_assoc_r : forall (P Q R : infseq T -> Prop) (s : infseq T),
  (P /\_ Q /\_ R) s ->
  ((P /\_ Q) /\_ R) s.
Proof.
move => P Q R s.
unfold and_tl.
move => H_and.
by break_and.
Qed.

Lemma not_and_not_or_tl : forall (P Q : infseq T -> Prop) (s : infseq T),
  ((~_ P) /\_ (~_ Q)) s ->
  (~_ (P \/_ Q)) s.
Proof.
move => P Q s.
unfold not_tl, and_tl, or_tl.
move => H_and H_or.
break_and.
by break_or_hyp.
Qed.

Lemma not_or_not_and_tl : forall (P Q : infseq T -> Prop) (s : infseq T),
  (~_ (P \/_ Q)) s ->
  ((~_ P) /\_ (~_ Q)) s.
Proof.
move => P Q s.
unfold not_tl, and_tl, or_tl.
move => H_not.
by split; move => H_p; case: H_not; [left|right].
Qed.

Lemma continuously_monotonic : forall (P Q : infseq T -> Prop),
  (forall s, P s -> Q s) ->
  forall s, continuously P s -> continuously Q s.
Proof.
move => P Q H_i s.
apply: eventually_monotonic_simple.
exact: always_monotonic.
Qed.

Lemma until_not_eventually_always :
  forall (J P : infseq T -> Prop) (s : infseq T),
  until J P s -> ~ eventually P s -> always J s.
Proof.
move => J P.
cofix c.
case => e s.
move => H_un H_ev.
apply until_Cons in H_un.
case: H_un => H_un.
  case H_ev.
  by constructor.
move: H_un => [H_j H_un].
constructor; first by [].
rewrite /=.
apply: c => //.
move => H_ev'.
case: H_ev.
by constructor 2.
Qed.

End Aux.
