Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.

Require Import NoAppendEntriesToSelfInterface.

Section NoAppendEntriesToSelf.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance noaetsi : no_append_entries_to_self_interface.
  Admitted.
End NoAppendEntriesToSelf.

