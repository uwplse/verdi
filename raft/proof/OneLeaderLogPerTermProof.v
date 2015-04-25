Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import OneLeaderLogPerTermInterface.

Section OneLeaderLogPerTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem one_leaderLog_per_term_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      one_leaderLog_per_term net.
  Admitted.

  Instance ollpti : one_leaderLog_per_term_interface.
  Proof.
    split. eauto using one_leaderLog_per_term_invariant.
  Qed.

End OneLeaderLogPerTerm.
