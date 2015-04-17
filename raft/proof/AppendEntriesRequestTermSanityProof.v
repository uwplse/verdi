Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import AppendEntriesRequestTermSanityInterface.

Section AppendEntriesRequestTermSanity.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance aertsi : append_entries_request_term_sanity_interface.
  Admitted.
End AppendEntriesRequestTermSanity.
