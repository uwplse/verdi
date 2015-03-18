Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import TermsAndIndicesFromOneInterface.

Section TermsAndIndicesFromOne.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance taifoi : terms_and_indices_from_one_interface.
  Admitted.
End TermsAndIndicesFromOne.