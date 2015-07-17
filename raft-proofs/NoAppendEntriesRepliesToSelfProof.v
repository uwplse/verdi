Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import SpecLemmas.

Require Import NoAppendEntriesRepliesToSelfInterface.

Section NoAppendEntriesRepliesToSelf.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  
  Instance noaertsi : no_append_entries_replies_to_self_interface.
  Admitted.


End NoAppendEntriesRepliesToSelf.

