Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import Raft.
Require Import VerdiTactics.

Section CandidatesVoteForSelves.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition candidates_vote_for_selves net :=
    forall h,
      type (nwState net h) = Candidate ->
      votedFor (nwState net h) = Some h.

  Ltac rewrite_state :=
    match goal with
      | [st : name -> raft_data,
              H : forall _, ?st _ = _  |- _] =>
        rewrite H in *
    end.

  Ltac come_to_jesus :=
    repeat break_match;
      simpl in *; try find_inversion; rewrite_state;
      repeat break_if; subst; eauto; simpl in *; try discriminate.
  
  Theorem candidates_vote_for_selves_do_leader :
    raft_net_invariant_do_leader (candidates_vote_for_selves).
  Proof.
    unfold raft_net_invariant_do_leader, candidates_vote_for_selves. intros.
    unfold doLeader, advanceCommitIndex in *.
    come_to_jesus.
  Qed.

  Lemma candidates_vote_for_selves_client_request :
    raft_net_invariant_client_request (candidates_vote_for_selves).
  Proof.
    unfold raft_net_invariant_client_request, candidates_vote_for_selves.
    intros. unfold handleClientRequest in *.
    come_to_jesus.
  Qed.

  Lemma candidates_vote_for_selves_timeout :
    raft_net_invariant_timeout candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_timeout, candidates_vote_for_selves. intros.
    unfold handleTimeout, tryToBecomeLeader in *.
    come_to_jesus.
  Qed.

  Lemma candidates_vote_for_selves_append_entries :
    raft_net_invariant_append_entries candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_append_entries, candidates_vote_for_selves. intros.
    unfold handleAppendEntries, advanceCurrentTerm in *.
    come_to_jesus.
  Qed.

  Lemma candidates_vote_for_selves_append_entries_reply :
    raft_net_invariant_append_entries_reply candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_append_entries_reply, candidates_vote_for_selves. intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    come_to_jesus.
  Qed.

  Lemma candidates_vote_for_selves_request_vote :
    raft_net_invariant_request_vote candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_request_vote, candidates_vote_for_selves. intros.
    unfold handleRequestVote, advanceCurrentTerm in *.
    come_to_jesus. exfalso. find_apply_hyp_hyp. congruence.
  Qed.

  Lemma candidates_vote_for_selves_request_vote_reply :
    raft_net_invariant_request_vote_reply candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_request_vote_reply, candidates_vote_for_selves. intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    come_to_jesus.
  Qed.
  
  Lemma candidates_vote_for_selves_do_generic_server :
    raft_net_invariant_do_generic_server candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_do_generic_server, candidates_vote_for_selves. intros.
    unfold doGenericServer in *.
    come_to_jesus.
  Qed.
  
  Lemma candidates_vote_for_selves_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, candidates_vote_for_selves. intros.
    repeat find_reverse_higher_order_rewrite; eauto.
  Qed.

  Lemma candidates_vote_for_selves_reboot :
    raft_net_invariant_reboot candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_reboot, candidates_vote_for_selves. intros.
    repeat find_higher_order_rewrite. simpl in *. subst. unfold reboot in *.
    break_if; simpl in *; eauto; discriminate.
  Qed.

  Theorem candidates_vote_for_selves_init :
    raft_net_invariant_init candidates_vote_for_selves.
  Proof.
    unfold raft_net_invariant_init, candidates_vote_for_selves, step_m_init.
    simpl in *. intros; discriminate.
  Qed.
    
  Theorem candidates_vote_for_selves_invariant :
    forall net,
      raft_intermediate_reachable net ->
      candidates_vote_for_selves net.
  Proof.
    intros.
    eapply raft_net_invariant; eauto.
    - apply candidates_vote_for_selves_init.
    - apply candidates_vote_for_selves_client_request.
    - apply candidates_vote_for_selves_timeout.
    - apply candidates_vote_for_selves_append_entries.
    - apply candidates_vote_for_selves_append_entries_reply.
    - apply candidates_vote_for_selves_request_vote.
    - apply candidates_vote_for_selves_request_vote_reply.
    - apply candidates_vote_for_selves_do_leader.
    - apply candidates_vote_for_selves_do_generic_server.
    - apply candidates_vote_for_selves_state_same_packet_subset.
    - apply candidates_vote_for_selves_reboot.
  Qed.
  
End CandidatesVoteForSelves.
