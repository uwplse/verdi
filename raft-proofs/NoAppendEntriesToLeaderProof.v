Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.

Require Import NoAppendEntriesToLeaderInterface.

Section NoAppendEntriesToLeader.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance noaetli : no_append_entries_to_leader_interface.
  Admitted.
End NoAppendEntriesToLeader.

