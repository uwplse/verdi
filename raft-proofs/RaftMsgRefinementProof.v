Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Sumbool.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.

Require Import RaftMsgRefinementInterface.

Section RaftMsgRefinement.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance rmri : raft_msg_refinement_interface.
  Admitted.
End RaftMsgRefinement.