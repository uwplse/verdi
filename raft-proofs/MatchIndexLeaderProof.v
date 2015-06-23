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

Require Import MatchIndexLeaderInterface.

Section MatchIndexLeader.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Instance mili : match_index_leader_interface.
  Admitted.
End MatchIndexLeader.