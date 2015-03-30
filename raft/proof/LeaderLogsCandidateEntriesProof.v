Require Import List.
Import ListNotations.

Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import RefinementCommonDefinitions.

Require Import LeaderLogsCandidateEntriesInterface.

Section CandidateEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma leaderLogs_candidateEntries_init :
    refined_raft_net_invariant_init leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_client_request :
    refined_raft_net_invariant_client_request leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_timeout :
    refined_raft_net_invariant_timeout leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_reboot :
    refined_raft_net_invariant_reboot leaderLogs_candidateEntries.
  Admitted.

  Lemma leaderLogs_candidateEntries_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_candidateEntries net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_candidateEntries_init.
    - apply leaderLogs_candidateEntries_client_request.
    - apply leaderLogs_candidateEntries_timeout.
    - apply leaderLogs_candidateEntries_append_entries.
    - apply leaderLogs_candidateEntries_append_entries_reply.
    - apply leaderLogs_candidateEntries_request_vote.
    - apply leaderLogs_candidateEntries_request_vote_reply.
    - apply leaderLogs_candidateEntries_do_leader.
    - apply leaderLogs_candidateEntries_do_generic_server.
    - apply leaderLogs_candidateEntries_state_same_packet_subset.
    - apply leaderLogs_candidateEntries_reboot.
  Qed.


  Instance llcei : leaderLogs_candidate_entries_interface.
  Admitted.
End CandidateEntriesInterface.
