Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.

Require Import LeaderLogsContiguousInterface.

Section LeaderLogsContiguous.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma leaderLogs_contiguous_init :
    refined_raft_net_invariant_init leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_client_request :
    refined_raft_net_invariant_client_request leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_timeout :
    refined_raft_net_invariant_timeout leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_reboot :
    refined_raft_net_invariant_reboot leaderLogs_contiguous.
  Admitted.

  Lemma leaderLogs_contiguous_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_contiguous net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_contiguous_init.
    - apply leaderLogs_contiguous_client_request.
    - apply leaderLogs_contiguous_timeout.
    - apply leaderLogs_contiguous_append_entries.
    - apply leaderLogs_contiguous_append_entries_reply.
    - apply leaderLogs_contiguous_request_vote.
    - apply leaderLogs_contiguous_request_vote_reply.
    - apply leaderLogs_contiguous_do_leader.
    - apply leaderLogs_contiguous_do_generic_server.
    - apply leaderLogs_contiguous_state_same_packet_subset.
    - apply leaderLogs_contiguous_reboot.
  Qed.

  Instance llci : leaderLogs_contiguous_interface : Prop.
  Proof.
    split.
    exact leaderLogs_contiguous_invariant.
  Qed.
End LeaderLogsContiguous.
