Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import LeadersHaveLeaderLogsInterface.
Require Import EveryEntryWasCreatedHostLogInterface.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhlli : leaders_have_leaderLogs_interface}.
  Context {rri : raft_refinement_interface}.

  Lemma every_entry_was_created_host_log_init :
    refined_raft_net_invariant_init every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_client_request :
    refined_raft_net_invariant_client_request every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_timeout :
    refined_raft_net_invariant_timeout every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_append_entries :
    refined_raft_net_invariant_append_entries every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_request_vote :
    refined_raft_net_invariant_request_vote every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_do_leader :
    refined_raft_net_invariant_do_leader every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_do_generic_server :
    refined_raft_net_invariant_do_generic_server every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_reboot :
    refined_raft_net_invariant_reboot every_entry_was_created_host_log.
  Admitted.

  Lemma every_entry_was_created_host_log_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      every_entry_was_created_host_log net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply every_entry_was_created_host_log_init.
    - apply every_entry_was_created_host_log_client_request.
    - apply every_entry_was_created_host_log_timeout.
    - apply every_entry_was_created_host_log_append_entries.
    - apply every_entry_was_created_host_log_append_entries_reply.
    - apply every_entry_was_created_host_log_request_vote.
    - apply every_entry_was_created_host_log_request_vote_reply.
    - apply every_entry_was_created_host_log_do_leader.
    - apply every_entry_was_created_host_log_do_generic_server.
    - apply every_entry_was_created_host_log_state_same_packet_subset.
    - apply every_entry_was_created_host_log_reboot.
  Qed.

  Instance eewchli : every_entry_was_created_host_log_interface.
  Admitted.
End EveryEntryWasCreated.
