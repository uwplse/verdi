Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Omega.

Require Import Util.
Require Import Net.
Require Import Raft.
Require Import VerdiTactics.
Require Import CommonTheorems.

Require Import PrevLogLeaderSublogInterface.

Section PrevLogLeaderSublogProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance pllsi : prevLog_leader_sublog_interface.
  Proof.
    constructor.
  Admitted.
End PrevLogLeaderSublogProof.
