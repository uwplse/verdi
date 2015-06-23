Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import MatchIndexSanityInterface.

Section MatchIndexSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance matchisi : match_index_sanity_interface.
  Admitted.
End MatchIndexSanity.