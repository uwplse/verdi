Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonTheorems.

Require Import VerdiTactics.

Require Import VotesLeCurrentTermInterface.

Section VotesCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma votes_le_current_term_client_request :
    refined_raft_net_invariant_client_request votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_timeout :
    refined_raft_net_invariant_timeout votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_append_entries :
    refined_raft_net_invariant_append_entries votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_request_vote :
    refined_raft_net_invariant_request_vote votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_do_leader :
    refined_raft_net_invariant_do_leader votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_do_generic_server :
    refined_raft_net_invariant_do_generic_server votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votes_le_currentTerm.
  Admitted.

  Lemma votes_le_current_term_reboot :
    refined_raft_net_invariant_reboot votes_le_currentTerm.
  Admitted.

  Theorem votes_le_current_term_init :
    refined_raft_net_invariant_init votes_le_currentTerm.
  Admitted.

  Theorem votes_le_current_term_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      votes_le_currentTerm net.
  Proof.
    intros.
    eapply refined_raft_net_invariant; eauto.
    - apply votes_le_current_term_init.
    - apply votes_le_current_term_client_request.
    - apply votes_le_current_term_timeout.
    - apply votes_le_current_term_append_entries.
    - apply votes_le_current_term_append_entries_reply.
    - apply votes_le_current_term_request_vote.
    - apply votes_le_current_term_request_vote_reply.
    - apply votes_le_current_term_do_leader.
    - apply votes_le_current_term_do_generic_server.
    - apply votes_le_current_term_state_same_packet_subset.
    - apply votes_le_current_term_reboot.
  Qed.

  Instance vlcti : votes_le_current_term_interface.
  Proof.
    split.
    auto using votes_le_current_term_invariant.
  Qed.
End VotesCorrect.
