Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.

Require Import LeaderLogsLogMatchingInterface.

Section LeaderLogsLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma leaderLogs_entries_match_init :
    refined_raft_net_invariant_init leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_client_request :
    refined_raft_net_invariant_client_request leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_timeout :
    refined_raft_net_invariant_timeout leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_reboot :
    refined_raft_net_invariant_reboot leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_entries_match_host net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_entries_match_init.
    - apply leaderLogs_entries_match_client_request.
    - apply leaderLogs_entries_match_timeout.
    - apply leaderLogs_entries_match_append_entries.
    - apply leaderLogs_entries_match_append_entries_reply.
    - apply leaderLogs_entries_match_request_vote.
    - apply leaderLogs_entries_match_request_vote_reply.
    - apply leaderLogs_entries_match_do_leader.
    - apply leaderLogs_entries_match_do_generic_server.
    - apply leaderLogs_entries_match_state_same_packet_subset.
    - apply leaderLogs_entries_match_reboot.
  Qed.

  Instance lllmi : leaderLogs_entries_match_interface : Prop.
  Proof.
    split.
    exact leaderLogs_entries_match_invariant.
  Qed.
End LeaderLogsLogMatching.