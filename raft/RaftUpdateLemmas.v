Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.

Require Export UpdateLemmas.

(* This file redefines these tactics so that they correctly refer to Raft's name_eq_dec.
   This is a horrible hack. *)

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
