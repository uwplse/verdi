Require Import List.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.

Require Import AllEntriesLeaderLogsInterface.

Section AllEntriesLeaderLogs.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma all_entries_leader_logs_init :
    refined_raft_net_invariant_init all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_client_request :
    refined_raft_net_invariant_client_request all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_timeout :
    refined_raft_net_invariant_timeout all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_append_entries :
    refined_raft_net_invariant_append_entries all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_request_vote :
    refined_raft_net_invariant_request_vote all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_do_leader :
    refined_raft_net_invariant_do_leader all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_do_generic_server :
    refined_raft_net_invariant_do_generic_server all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset all_entries_leader_logs.
  Admitted.

  Lemma all_entries_leader_logs_reboot :
    refined_raft_net_invariant_reboot all_entries_leader_logs.
  Admitted.

  Theorem all_entries_leader_logs_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      all_entries_leader_logs net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply all_entries_leader_logs_init.
    - apply all_entries_leader_logs_client_request.
    - apply all_entries_leader_logs_timeout.
    - apply all_entries_leader_logs_append_entries.
    - apply all_entries_leader_logs_append_entries_reply.
    - apply all_entries_leader_logs_request_vote.
    - apply all_entries_leader_logs_request_vote_reply.
    - apply all_entries_leader_logs_do_leader.
    - apply all_entries_leader_logs_do_generic_server.
    - apply all_entries_leader_logs_state_same_packet_subset.
    - apply all_entries_leader_logs_reboot.
  Qed.

  Instance aelli :  all_entries_leader_logs_interface.
  Proof.
    split.
    exact all_entries_leader_logs_invariant.
  Qed.
End AllEntriesLeaderLogs.
