Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import RefinementCommonDefinitions.
Require Import RefinementCommonTheorems.

Require Import CandidateEntriesInterface.
Require Import CroniesCorrectInterface.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import LeaderLogsCandidateEntriesInterface.

Section CandidateEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {cci : cronies_correct_interface}.
  Context {cei : candidate_entries_interface}.

  Lemma leaderLogs_candidateEntries_init :
    refined_raft_net_invariant_init leaderLogs_candidateEntries.
  Proof.
    unfold refined_raft_net_invariant_init, leaderLogs_candidateEntries.
    simpl. intuition.
  Qed.

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
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, leaderLogs_candidateEntries.
    simpl. intuition.
    find_copy_apply_lem_hyp candidate_entries_invariant; auto.
    unfold CandidateEntries, candidateEntries_host_invariant in *.
    eapply candidateEntries_ext; try eassumption.
    subst.
    repeat find_higher_order_rewrite.
    find_rewrite_lem update_fun_comm. simpl in *.
    destruct (name_eq_dec (pDst p) h).
    - rewrite_update.
      find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
      intuition.
      + eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
      + subst. find_erewrite_lem handleRequestVoteReply_log.
        eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
    - rewrite_update.
      eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
  Qed.

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
