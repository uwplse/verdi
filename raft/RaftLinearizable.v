Require Import List.
Import ListNotations.

Require Import Net.
Require Import Util.

Require Import Raft.
Require Import Linearizability.

Section RaftLinearizable.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition key : Type := nat * nat.

  Fixpoint import (tr : list (name * (raft_input + list raft_output)))
  : list (op key) :=
    match tr with
      | [] => []
      | (_, (inl (ClientRequest c id cmd))) :: xs =>
        I _ (c, id) :: import xs
      | (_, (inr l)) :: xs =>
        filterMap (fun x =>
                     match x with
                       | ClientResponse c id cmd => Some (O _ (c, id))
                       | _ => None
                     end) l ++ import xs
      | _ :: xs => import xs
  end.

(*
  Definition export (env : key -> option input) (l : list (IR key)) : option (list (input * output)) :=
    (*
    map (fun x => (match x with
                      | IRI _ k =>
                      | IRO _ k => O _ k
                      | IRU _ k => O _ k
                    end)) l. *)
*)

(*
  Definition raft_linearizable
             (tr : list (name * (input + list output))) : Prop :=
    exists l',
      equivalent (import tr) l' /\
*)
End RaftLinearizable.