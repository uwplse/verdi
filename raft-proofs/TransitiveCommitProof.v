Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Sumbool.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import RaftRefinementInterface.

Require Import RefinementCommonDefinitions.

Require Import LeaderCompletenessInterface.
Require Import RefinedLogMatchingLemmasInterface.

Require Import TransitiveCommitInterface.

Section TransitiveCommit.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  
  Context {rlmli : refined_log_matching_lemmas_interface}.

  Theorem transitive_commit_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      transitive_commit net.
  Proof.
    unfold transitive_commit, committed. intros.
    break_exists_name h'; exists h'.
    break_exists_name e''; exists e''.
    intuition; eauto.
    eapply (entries_match_invariant net h h'); eauto.
  Qed.

  Instance tci : transitive_commit_interface.
  Proof.
    split.
    exact transitive_commit_invariant.
  Qed.
End TransitiveCommit.
