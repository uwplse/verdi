Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.

Section RaftLinearizableDefinitions.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition project_input_keys (tr : list (name * (raft_input + list raft_output))) : list (nat * nat) :=
    filterMap (fun x => match x with
                          | (_, inl (ClientRequest client id _)) => Some (client, id)
                          | _ => None
                        end) tr.

  Definition input_correct (tr : list (name * (raft_input + list raft_output))) : Prop :=
    NoDup (project_input_keys tr).
End RaftLinearizableDefinitions.