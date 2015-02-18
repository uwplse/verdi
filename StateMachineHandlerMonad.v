Require Import List.
Import ListNotations.

(*
This file is very similar to HandlerMonad.v, but supports step_1
handlers. It's just a state monad: no sending messages allowed. The
output of the handler is a singleton instead of a list and is given as
the return value.
*)

Definition GenHandler1 (S A : Type) : Type := S -> A * S % type.

Definition ret {S A : Type} (a : A) : GenHandler1 S A := fun s => (a, s).

Definition bind {S A B : Type} (m : GenHandler1 S A) (f : A -> GenHandler1 S B) : GenHandler1 S B :=
  fun s =>
    let '(a, s') := m s in
    let '(b, s'') := f a s' in
    (b, s'').

(* alias for ret *)
Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.

Definition modify {S} (f : S -> S) : GenHandler1 S unit := fun s => (tt, f s).

Definition put {S} (s : S) : GenHandler1 S unit := fun _ => (tt, s).

Definition get {S} : GenHandler1 S S := fun s => (s, s).

Definition runGenHandler1 {S A} (s : S) (h : GenHandler1 S A) :
  A * S % type :=
  h s.

Definition nop {S : Type} := @ret S _ tt.

Notation "a >> b" := (bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Definition when {S A} (b : bool) (m : GenHandler1 S A) : GenHandler1 S unit :=
  if b then m ;; ret tt else nop.

Ltac monad_unfold :=
  repeat unfold
         runGenHandler1,
         bind,
         write_output,
         get,
         when,
         put,
         nop,
         modify,
         ret in *.
