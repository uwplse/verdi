Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonTheorems.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import LeadersHaveLeaderLogsStrongInterface.

Section LeadersHaveLeaderLogsStrong.
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
    red; unfold leaders_have_leaderLogs_strong; intros;
    subst; simpl in *; find_higher_order_rewrite;
    update_destruct; subst; rewrite_update; eauto; simpl in *.

  Lemma handleAppendEntries_type :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (type st' = type st /\ currentTerm st' = currentTerm st /\ log st' = log st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleAppendEntriesReply_type :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      (type st' = type st /\ currentTerm st' = currentTerm st /\ log st' = log st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleRequestVote_type :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      (type st' = type st /\ currentTerm st' = currentTerm st /\ log st' = log st) \/
      type st' = Follower.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleClientRequest_type :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      type st' = type st /\ currentTerm st' = currentTerm st /\
      (log st' = log st \/ exists e, eTerm e = currentTerm st /\ log st' = e :: log st).
  Proof.
    intros. unfold handleClientRequest in *.
    repeat break_match; find_inversion; intuition eauto.
    simpl in *. right. eexists; simpl in *; intuition eauto.
    reflexivity.
  Qed.

  Lemma handleTimeout_type :
    forall h st out st' l,
      handleTimeout h st = (out, st', l) ->
      (type st' = type st /\ currentTerm st' = currentTerm st /\ log st' = log st) \/
      type st' = Candidate.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma doGenericServer_type :
    forall h st os st' ms,
      doGenericServer h st = (os, st', ms) ->
      type st' = type st /\ currentTerm st' = currentTerm st /\ log st' = log st.
  Proof.
    unfold doGenericServer.
    intros.
    repeat break_match; repeat find_inversion;
    use_applyEntries_spec; subst; simpl in *;
    auto.
  Qed.

  Lemma doLeader_type :
        forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      type st' = type st /\ currentTerm st' = currentTerm st /\ log st' = log st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma update_elections_data_client_request_leaderLogs :
    forall h st client id c,
      leaderLogs (update_elections_data_client_request h st client id c) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_client_request in *.
    intros. repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma update_elections_data_timeout_leaderLogs :
    forall h st,
      leaderLogs (update_elections_data_timeout h st) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; simpl in *; auto.
  Qed.

  Lemma update_elections_data_appendEntries_leaderLogs :
    forall h st t h' pli plt es ci,
      leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) =
      leaderLogs (fst st).
  Proof.
    intros.
    unfold update_elections_data_appendEntries.
    repeat break_match; subst; simpl in *; auto.
  Qed.
  
  Lemma update_elections_data_requestVote_leaderLogs :
    forall h h' t lli llt st,
      leaderLogs (update_elections_data_requestVote h h' t h' lli llt st) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_requestVote.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma leaders_have_leaderLogs_strong_appendEntries :
    refined_raft_net_invariant_append_entries leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_copy_apply_lem_hyp handleAppendEntries_type.
    rewrite update_elections_data_appendEntries_leaderLogs.
    intuition; try congruence; subst;
    repeat find_rewrite; eauto.
  Qed.
  
  Lemma leaders_have_leaderLogs_strong_appendEntriesReply :
    refined_raft_net_invariant_append_entries_reply leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_apply_lem_hyp handleAppendEntriesReply_type. intuition; try congruence.
    repeat find_rewrite. eauto.
  Qed.


  Lemma leaders_have_leaderLogs_strong_requestVote :
    refined_raft_net_invariant_request_vote leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_apply_lem_hyp handleRequestVote_type. intuition; try congruence.
    rewrite update_elections_data_requestVote_leaderLogs.
    repeat find_rewrite. eauto.
  Qed.
  
  
  Lemma leaders_have_leaderLogs_strong_requestVoteReply :
    refined_raft_net_invariant_request_vote_reply leaders_have_leaderLogs_strong.
  Proof.
    start.
    unfold update_elections_data_requestVoteReply.
    break_match; unfold raft_data in *;
    try solve [repeat find_rewrite; congruence].
    simpl in *.
    match goal with
      | |- context [ handleRequestVoteReply ?h ?st ?s ?t ?v ] =>
        pose proof handleRequestVoteReply_spec h st s t v (handleRequestVoteReply h st s t v)
    end. intuition; break_if; intuition; simpl in *; repeat find_rewrite; eauto; try congruence.
    eexists. exists []. intuition eauto. simpl in *. intuition.
  Qed.

  Lemma leaders_have_leaderLogs_strong_clientRequest :
    refined_raft_net_invariant_client_request leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_copy_apply_lem_hyp handleClientRequest_type.
    intuition; try congruence;
    rewrite update_elections_data_client_request_leaderLogs.
    - repeat find_rewrite. eauto.
    - break_exists. intuition. repeat find_rewrite.
      match goal with
        | h : name, H : forall _, type _ =  type _ -> _ |- _ =>
          specialize (H h); concludes
      end.
      break_exists.
      match goal with
        | _ : context [log _ = ?l1 ++ ?l2] |- _ =>
          exists l2, (x :: l1)
      end. intuition.
      + repeat find_rewrite. eauto.
      + simpl in *. intuition; subst; eauto.
  Qed.

  Lemma leaders_have_leaderLogs_strong_timeout :
    refined_raft_net_invariant_timeout leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_apply_lem_hyp handleTimeout_type. intuition; try congruence.
    rewrite update_elections_data_timeout_leaderLogs.
    repeat find_rewrite. eauto.
  Qed.


  Lemma leaders_have_leaderLogs_strong_doGenericServer :
    refined_raft_net_invariant_do_generic_server leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_apply_lem_hyp doGenericServer_type. intuition; try congruence.
    match goal with
      | [ H : forall _, _ -> exists _, _, h : name |- _ ] =>
        specialize (H h)
    end.
    repeat find_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_strong_doLeader :
    refined_raft_net_invariant_do_leader leaders_have_leaderLogs_strong.
  Proof.
    start.
    find_apply_lem_hyp doLeader_type. intuition; try congruence.
    match goal with
      | [ H : forall _, _ -> exists _, _, h : name |- _ ] =>
        specialize (H h)
    end.
    repeat find_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_strong_init :
    refined_raft_net_invariant_init leaders_have_leaderLogs_strong.
  Proof.
    red. unfold leaders_have_leaderLogs_strong, step_async_init.
    intros. simpl in *. congruence.
  Qed.

  Lemma leaders_have_leaderLogs_strong_state_same_packets_subset :
    refined_raft_net_invariant_state_same_packet_subset leaders_have_leaderLogs_strong.
  Proof.
    red. unfold leaders_have_leaderLogs_strong. intros.
    repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma leaders_have_leaderLogs_strong_reboot :
    refined_raft_net_invariant_reboot leaders_have_leaderLogs_strong.
  Proof.
    start. congruence.
  Qed.
  
  Instance lhllsi : leaders_have_leaderLogs_strong_interface.
  Proof.
    split.
    intros. eapply refined_raft_net_invariant; eauto.
    - apply leaders_have_leaderLogs_strong_init.
    - apply leaders_have_leaderLogs_strong_clientRequest.
    - apply leaders_have_leaderLogs_strong_timeout.
    - apply leaders_have_leaderLogs_strong_appendEntries.
    - apply leaders_have_leaderLogs_strong_appendEntriesReply.
    - apply leaders_have_leaderLogs_strong_requestVote.
    - apply leaders_have_leaderLogs_strong_requestVoteReply.
    - apply leaders_have_leaderLogs_strong_doLeader.
    - apply leaders_have_leaderLogs_strong_doGenericServer.
    - apply leaders_have_leaderLogs_strong_state_same_packets_subset.
    - apply leaders_have_leaderLogs_strong_reboot.
  Qed.
End LeadersHaveLeaderLogsStrong.
