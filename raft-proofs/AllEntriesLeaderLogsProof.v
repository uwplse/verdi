Require Import List.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AllEntriesLeaderLogsInterface.

Section AllEntriesLeaderLogs.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma leader_without_missing_entry_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_without_missing_entry net.
  Admitted.

  Lemma appendEntriesRequest_exists_leaderLog_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntriesRequest_exists_leaderLog net.
  Admitted.

  Lemma appendEntriesRequest_leaderLog_not_in_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntriesRequest_leaderLog_not_in net.
  Admitted.

  Lemma appendEntries_leader_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntries_leader net.
  Admitted.

  Lemma leaderLogs_leader_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_leader net.
  Admitted.

  Instance aelli :  all_entries_leader_logs_interface.
  Proof.
    split.
    intros.
    red.
    intuition.
    - auto using leader_without_missing_entry_invariant.
    - auto using appendEntriesRequest_exists_leaderLog_invariant.
    - auto using appendEntriesRequest_leaderLog_not_in_invariant.
    - auto using appendEntries_leader_invariant.
    - auto using leaderLogs_leader_invariant.
  Qed.
End AllEntriesLeaderLogs.
