Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CommonTheorems.
Require Import RefinementCommonTheorems.

Require Import AppendEntriesLeaderInterface.

Section AllEntriesLeaderLogs.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma appendEntries_leader_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntries_leader net.
  Admitted.

  Instance appendeli : append_entries_leader_interface.
  Proof.
    split.
    exact appendEntries_leader_invariant.
  Qed.
End AllEntriesLeaderLogs.