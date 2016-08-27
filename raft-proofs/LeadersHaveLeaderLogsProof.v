Require Import Raft.
Require Import RaftRefinementInterface.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import LeadersHaveLeaderLogsInterface.

Section LeadersHaveLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma handleRequestVoteReply_spec :
    forall h st h' t r st',
      st' = handleRequestVoteReply h st h' t r ->
      log st' = log st /\
      ((currentTerm st' = currentTerm st /\ type st' = type st) \/
       type st' = Follower \/ (type st = Candidate /\ type st' = Leader)).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition.
  Qed.

  Ltac start :=
    red; unfold leaders_have_leaderLogs; intros;
    subst; simpl in *; find_higher_order_rewrite;
    update_destruct; subst; rewrite_update; eauto; simpl in *.

  Lemma leaders_have_leaderLogs_appendEntries :
    refined_raft_net_invariant_append_entries leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp handleAppendEntries_type. intuition; try congruence.
    rewrite update_elections_data_appendEntries_leaderLogs.
    repeat find_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_appendEntriesReply :
    refined_raft_net_invariant_append_entries_reply leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp handleAppendEntriesReply_type. intuition; try congruence.
    repeat find_rewrite. eauto.
  Qed.


  Lemma leaders_have_leaderLogs_requestVote :
    refined_raft_net_invariant_request_vote leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp handleRequestVote_type. intuition; try congruence.
    rewrite leaderLogs_update_elections_data_requestVote.
    repeat find_rewrite. eauto.
  Qed.
  
  
  Lemma leaders_have_leaderLogs_requestVoteReply :
    refined_raft_net_invariant_request_vote_reply leaders_have_leaderLogs.
  Proof.
    start.
    unfold update_elections_data_requestVoteReply.
    break_match; unfold raft_data in *;
    try solve [repeat find_rewrite; congruence].
    simpl in *.
    match goal with
      | |- context [ handleRequestVoteReply ?h ?st ?s ?t ?v ] =>
        pose proof handleRequestVoteReply_spec h st s t v (handleRequestVoteReply h st s t v)
    end. intuition; break_if; intuition; simpl in *; repeat find_rewrite; eauto; congruence.
  Qed.

  Lemma leaders_have_leaderLogs_clientRequest :
    refined_raft_net_invariant_client_request leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp handleClientRequest_type. intuition; try congruence.
    rewrite update_elections_data_client_request_leaderLogs.
    repeat find_rewrite. eauto.
  Qed.


  Lemma leaders_have_leaderLogs_timeout :
    refined_raft_net_invariant_timeout leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp handleTimeout_type. intuition; try congruence.
    rewrite update_elections_data_timeout_leaderLogs.
    repeat find_rewrite. eauto.
  Qed.


  Lemma leaders_have_leaderLogs_doGenericServer :
    refined_raft_net_invariant_do_generic_server leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp doGenericServer_type. intuition; try congruence.
    match goal with
      | [ H : forall _, _ -> exists _, _, h : name |- _ ] =>
        specialize (H h)
    end.
    repeat find_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_doLeader :
    refined_raft_net_invariant_do_leader leaders_have_leaderLogs.
  Proof.
    start.
    find_apply_lem_hyp doLeader_type. intuition; try congruence.
    match goal with
      | [ H : forall _, _ -> exists _, _, h : name |- _ ] =>
        specialize (H h)
    end.
    repeat find_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_init :
    refined_raft_net_invariant_init leaders_have_leaderLogs.
  Proof.
    red. unfold leaders_have_leaderLogs, step_async_init.
    intros. simpl in *. congruence.
  Qed.

  Lemma leaders_have_leaderLogs_state_same_packets_subset :
    refined_raft_net_invariant_state_same_packet_subset leaders_have_leaderLogs.
  Proof.
    red. unfold leaders_have_leaderLogs. intros.
    repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_reboot :
    refined_raft_net_invariant_reboot leaders_have_leaderLogs.
  Proof.
    start. congruence.
  Qed.
  
  Instance lhlli : leaders_have_leaderLogs_interface.
  Proof.
    split.
    intros. eapply refined_raft_net_invariant; eauto.
    - apply leaders_have_leaderLogs_init.
    - apply leaders_have_leaderLogs_clientRequest.
    - apply leaders_have_leaderLogs_timeout.
    - apply leaders_have_leaderLogs_appendEntries.
    - apply leaders_have_leaderLogs_appendEntriesReply.
    - apply leaders_have_leaderLogs_requestVote.
    - apply leaders_have_leaderLogs_requestVoteReply.
    - apply leaders_have_leaderLogs_doLeader.
    - apply leaders_have_leaderLogs_doGenericServer.
    - apply leaders_have_leaderLogs_state_same_packets_subset.
    - apply leaders_have_leaderLogs_reboot.
  Qed.
End LeadersHaveLeaderLogs.
