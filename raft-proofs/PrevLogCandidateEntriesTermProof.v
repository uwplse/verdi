Require Import Raft.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RaftRefinementInterface.
Require Import CroniesTermInterface.

Require Import CroniesCorrectInterface.
Require Import CandidateEntriesInterface.

Require Import RefinementSpecLemmas.
Require Import RefinementCommonTheorems.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import PrevLogCandidateEntriesTermInterface.

Section PrevLogCandidateEntriesTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {cei : candidate_entries_interface}.
  Context {cti : cronies_term_interface}.
  Context {cci : cronies_correct_interface}.

  Lemma prevLog_candidateEntriesTerm_init :
    refined_raft_net_invariant_init prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_init, prevLog_candidateEntriesTerm.
    simpl. intuition.
  Qed.

  Lemma candidateEntriesTerm_ext : forall t sigma sigma',
      (forall h, sigma' h = sigma h) ->
      candidateEntriesTerm t sigma ->
      candidateEntriesTerm t sigma'.
  Proof.
    unfold candidateEntriesTerm.
    intros. break_exists_exists.
    repeat find_higher_order_rewrite. intuition.
  Qed.

  Lemma candidateEntriesTerm_same : forall st st' t,
       candidateEntriesTerm t st ->
       (forall h, cronies (fst (st' h)) = cronies (fst (st h))) ->
       (forall h, currentTerm (snd (st' h)) = currentTerm (snd (st h))) ->
       (forall h, type (snd (st' h)) = type (snd (st h))) ->
       candidateEntriesTerm t st'.
  Proof.
    unfold candidateEntriesTerm.
    intros. break_exists_exists.
    repeat find_higher_order_rewrite.
    intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
      | [  |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma prevLog_candidateEntriesTerm_client_request :
    refined_raft_net_invariant_client_request prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_client_request, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - eapply candidateEntriesTerm_ext; eauto.
      eapply candidateEntriesTerm_same; eauto; intros;
      update_destruct; auto.
      + now erewrite update_elections_data_client_request_cronies by eauto.
      + find_apply_lem_hyp handleClientRequest_type. intuition.
      + find_apply_lem_hyp handleClientRequest_type. intuition.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and. subst. simpl in *.
      exfalso. eapply handleClientRequest_no_append_entries; eauto.
      find_rewrite. eauto 10.
  Qed.

  Lemma update_elections_data_timeout_cronies :
    forall h d out d' l t,
      handleTimeout h (snd d) = (out, d', l) ->
      cronies (update_elections_data_timeout h d) t = cronies (fst d) t \/
      (t = currentTerm d' /\ type d' = Candidate /\
       cronies (update_elections_data_timeout h d) t = votesReceived d').
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; repeat find_inversion; simpl; auto.
    break_match; auto.
  Qed.

  Lemma handleClientRequest_preserves_candidateEntriesTerm:
    forall net h d t out l,
      refined_raft_intermediate_reachable net ->
      handleTimeout h (snd (nwState net h)) = (out, d, l) ->
      candidateEntriesTerm t (nwState net) ->
      candidateEntriesTerm t
                           (update (nwState net) h
                                   (update_elections_data_timeout h (nwState net h), d)).
  Proof.
    unfold candidateEntriesTerm.
    intros.
    break_exists_exists. break_and.
    match goal with
    | [ H : handleTimeout _ _ = _ |- _ ] =>
      pose proof H;
        eapply update_elections_data_timeout_cronies with (t := t) in H
    end. break_or_hyp.
    - update_destruct; auto.
      find_copy_apply_lem_hyp handleTimeout_type_strong.
      intuition; repeat find_rewrite; auto.
      find_apply_lem_hyp wonElection_exists_voter.
      break_exists.
      find_apply_lem_hyp in_dedup_was_in.
      find_copy_apply_lem_hyp cronies_term_invariant; auto.
      simpl in *.
      omega.
    - update_destruct; auto.
      find_copy_apply_lem_hyp handleTimeout_type_strong.
      find_apply_lem_hyp wonElection_exists_voter.
      break_exists.
      find_apply_lem_hyp in_dedup_was_in.
      find_copy_apply_lem_hyp cronies_term_invariant; auto.
      intuition; subst; repeat find_rewrite; auto;
      simpl in *; omega.
  Qed.

  Lemma prevLog_candidateEntriesTerm_timeout :
    refined_raft_net_invariant_timeout prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_timeout, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - eapply candidateEntriesTerm_ext; eauto.
      eapply handleClientRequest_preserves_candidateEntriesTerm; eauto.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      subst. simpl in *.
      exfalso. eapply handleTimeout_not_is_append_entries; eauto.
      find_rewrite. eauto 10.
  Qed.

  Lemma handleAppendEntries_preserves_candidateEntriesTerm :
    forall net h t n pli plt es ci d m t',
      handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) ->
      refined_raft_intermediate_reachable net ->
      candidateEntriesTerm t' (nwState net) ->
      candidateEntriesTerm t' (update (nwState net) h
                                 (update_elections_data_appendEntries
                                    h
                                    (nwState net h) t n pli plt es ci, d)).
  Proof.
    unfold candidateEntriesTerm.
    intros.
    break_exists_exists. break_and.
    update_destruct.
    - rewrite update_elections_data_appendEntries_cronies.
      find_apply_lem_hyp handleAppendEntries_type.
      intuition; subst; repeat find_rewrite; auto.
      discriminate.
    - intuition.
  Qed.

  Lemma prevLog_candidateEntriesTerm_append_entries :
    refined_raft_net_invariant_append_entries prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_append_entries, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
      eapply candidateEntriesTerm_ext; eauto.
      eapply handleAppendEntries_preserves_candidateEntriesTerm; eauto.
    - exfalso. eapply handleAppendEntries_not_append_entries; eauto.
      simpl in *. subst. eauto 10.
  Qed.

  Lemma handleAppendEntriesReply_preserves_candidateEntriesTerm :
  forall net h h' t es r st' ms t',
    handleAppendEntriesReply h (snd (nwState net h)) h' t es r = (st', ms) ->
    refined_raft_intermediate_reachable net ->
    candidateEntriesTerm t' (nwState net) ->
    candidateEntriesTerm t' (update (nwState net) h (fst (nwState net h), st')).
  Proof.
    unfold candidateEntriesTerm.
    intros. break_exists_exists.
    find_apply_lem_hyp handleAppendEntriesReply_type.
    update_destruct.
    - intuition; repeat find_rewrite; auto. discriminate.
    - auto.
  Qed.

  Lemma prevLog_candidateEntriesTerm_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
      eapply candidateEntriesTerm_ext; eauto.
      eauto using handleAppendEntriesReply_preserves_candidateEntriesTerm.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      find_apply_lem_hyp handleAppendEntriesReply_packets.
      subst. simpl in *. intuition.
  Qed.

  Lemma update_elections_data_requestVote_cronies_same :
    forall h h' t lli llt st,
      cronies (update_elections_data_requestVote h h' t h' lli llt st) =
      cronies (fst st).
  Proof.
    unfold update_elections_data_requestVote.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma advanceCurrentTerm_same_or_type_follower :
    forall st t,
      advanceCurrentTerm st t = st \/
      type (advanceCurrentTerm st t) = Follower.
  Proof.
    unfold advanceCurrentTerm.
    intros. repeat break_match; auto.
  Qed.

  Lemma handleRV_advanceCurrentTerm_preserves_candidateEntriesTerm :
    forall net h h' t lli llt t',
      candidateEntriesTerm t' (nwState net) ->
      candidateEntriesTerm t'
                       (update (nwState net) h
                               (update_elections_data_requestVote h h' t h' lli llt (nwState net h),
                                advanceCurrentTerm (snd (nwState net h)) t)).
  Proof.
    unfold candidateEntriesTerm.
    intros.
    break_exists_exists.
    update_destruct; intuition.
    - now rewrite update_elections_data_requestVote_cronies_same.
    - intros.
      match goal with
      | [ H : context [advanceCurrentTerm ?st ?t] |- _ ] =>
        pose proof advanceCurrentTerm_same_or_type_follower st t
      end.
      intuition.
      + repeat find_rewrite. auto.
      + congruence.
  Qed.

  Lemma handleRequestVote_preserves_candidateEntriesTerm :
    forall net h h' t lli llt d t' m,
      handleRequestVote h (snd (nwState net h)) t h' lli llt = (d, m) ->
      candidateEntriesTerm t' (nwState net) ->
      candidateEntriesTerm t' (update (nwState net) h
                                 (update_elections_data_requestVote
                                    h h' t h' lli llt (nwState net h), d)).
  Proof.
    unfold candidateEntriesTerm.
    intros.
    break_exists_exists.
    update_destruct; intuition.
    - now rewrite update_elections_data_requestVote_cronies_same.
    - unfold handleRequestVote, advanceCurrentTerm in *.
      repeat break_match; do_bool; repeat find_inversion; simpl in *; break_and; try discriminate; auto.
  Qed.

  Lemma prevLog_candidateEntriesTerm_request_vote :
    refined_raft_net_invariant_request_vote prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_request_vote, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
      eapply candidateEntriesTerm_ext; eauto.
      eapply handleRequestVote_preserves_candidateEntriesTerm; eauto.
    - exfalso. eapply handleRequestVote_no_append_entries; eauto.
      simpl in *. subst. eauto 10.
  Qed.

  Lemma handleRequestVoteReply_preserves_candidateEntriesTerm :
    forall net h h' t r st' t',
      handleRequestVoteReply h (snd (nwState net h)) h' t r = st' ->
      refined_raft_intermediate_reachable net ->
      candidateEntriesTerm t' (nwState net) ->
      candidateEntriesTerm t' (update (nwState net) h
                                 (update_elections_data_requestVoteReply h h' t r (nwState net h),
                                  st')).
  Proof.
    unfold candidateEntriesTerm.
    intros.
    break_exists_exists.
    update_destruct; auto.
    break_and.
    unfold raft_data in *. simpl in *.
    unfold update_elections_data_requestVoteReply.
    match goal with
    | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
      remember (handleRequestVoteReply h st h' t r) as new_state
    end; find_copy_apply_lem_hyp handleRequestVoteReply_spec.
    repeat (break_match); intuition; repeat find_rewrite; intuition;
    simpl; break_if; auto.
    - find_apply_lem_hyp cronies_correct_invariant.
      unfold cronies_correct in *. intuition.
      unfold votes_received_leaders in *.
      match goal with
      | H :  Leader = _ |- _ =>
        symmetry in H
      end. find_apply_hyp_hyp.
      eapply wonElection_no_dup_in;
        eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
    - destruct (serverType_eq_dec (type (snd (nwState net x))) Leader); intuition.
      find_apply_lem_hyp cronies_correct_invariant; auto.
      eapply wonElection_no_dup_in;
        eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
  Qed.

  Lemma prevLog_candidateEntriesTerm_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp.
    find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
    eapply candidateEntriesTerm_ext; eauto.
    subst.
    eapply handleRequestVoteReply_preserves_candidateEntriesTerm; eauto.
  Qed.

  Lemma doLeader_preserves_candidateEntriesTerm :
    forall net gd d h os d' ms t',
      nwState net h = (gd, d) ->
      doLeader d h = (os, d', ms) ->
      candidateEntriesTerm t' (nwState net) ->
      candidateEntriesTerm t' (update (nwState net) h (gd, d')).
  Proof.
    unfold candidateEntriesTerm.
    intros. break_exists_exists.
    break_and.
    update_destruct; auto.
    split.
    - match goal with
      | [ H : nwState ?net ?h = (?x, _) |- _ ] =>
        replace (x) with (fst (nwState net h)) in * by (rewrite H; auto)
      end.
      intuition.
    - match goal with
      | [ H : nwState ?net ?h = (_, ?x) |- _ ] =>
        replace (x) with (snd (nwState net h)) in * by (rewrite H; auto); clear H
      end.
      find_apply_lem_hyp doLeader_type.
      intuition. subst. repeat find_rewrite.
      auto.
  Qed.

  Lemma getNextIndex_ext :
    forall st st' h,
      nextIndex st' = nextIndex st ->
      log st' = log st ->
      getNextIndex st' h = getNextIndex st h.
  Proof.
    unfold getNextIndex.
    intros.
    repeat find_rewrite.
    auto.
  Qed.

  Lemma replicaMessage_ext :
    forall st st' h h',
      nextIndex st' = nextIndex st ->
      log st' = log st ->
      currentTerm st' = currentTerm st ->
      commitIndex st' = commitIndex st ->
      replicaMessage st' h h' = replicaMessage st h h'.
  Proof.
    unfold replicaMessage.
    intros.
    repeat break_match; repeat tuple_inversion; repeat find_rewrite;
    erewrite getNextIndex_ext in * by eauto; congruence.
  Qed.

  Lemma prevLog_candidateEntriesTerm_do_leader :
    refined_raft_net_invariant_do_leader prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_do_leader, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - find_apply_hyp_hyp.
      eapply candidateEntriesTerm_ext; eauto.
      eapply doLeader_preserves_candidateEntriesTerm; eauto.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      subst. simpl in *.
      find_copy_eapply_lem_hyp doLeader_messages; eauto.
      break_and. intuition.
      + omega.
      + break_exists. break_and.
        red.
        find_apply_lem_hyp candidate_entries_invariant.
        unfold CandidateEntries, candidateEntries_host_invariant in *.
        find_apply_lem_hyp findAtIndex_elim. break_and.
        match goal with
        | [ H : nwState ?net ?h = (?y, ?x) |- _ ] =>
          replace (x) with (snd (nwState net h)) in * by (rewrite H; auto);
          replace (y) with (fst (nwState net h)) in * by (rewrite H; auto)
        end.

        eapply_prop_hyp In In.
        subst.
        find_eapply_lem_hyp (doLeader_preserves_candidateEntries); eauto.

        match goal with
        | [ H : nwState ?net ?h = (?y, ?x) |- _ ] => clear H
        end.

        unfold candidateEntries in *. break_exists_exists.
        find_higher_order_rewrite.
        update_destruct; auto.
  Qed.

  Lemma doGenericServer_preserves_candidateEntriesTerm :
    forall net gd d h os d' ms t,
      nwState net h = (gd, d) ->
      doGenericServer h d = (os, d', ms) ->
      candidateEntriesTerm t (nwState net) ->
      candidateEntriesTerm t (update (nwState net) h (gd, d')).
  Proof.
    intros.
    find_apply_lem_hyp doGenericServer_type. break_and.
    eapply candidateEntriesTerm_same; eauto.
    - intros. update_destruct; auto.
      find_rewrite. simpl. auto.
    - intros. update_destruct; auto.
      repeat find_rewrite.  auto.
    - intros. update_destruct; auto.
      repeat find_rewrite.  auto.
  Qed.

  Lemma prevLog_candidateEntriesTerm_do_generic_server :
    refined_raft_net_invariant_do_generic_server prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp. break_or_hyp.
    - eapply candidateEntriesTerm_ext; eauto.
      eapply doGenericServer_preserves_candidateEntriesTerm; eauto.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      subst. simpl in *.
      find_apply_lem_hyp doGenericServer_packets. subst. simpl in *. intuition.
  Qed.

  Lemma prevLog_candidateEntriesTerm_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, prevLog_candidateEntriesTerm.
    simpl. intros.
    find_apply_hyp_hyp.
    eapply candidateEntriesTerm_ext with (sigma := (nwState net)).
    - auto.
    - eauto.
  Qed.

  Lemma prevLog_candidateEntriesTerm_reboot :
    refined_raft_net_invariant_reboot prevLog_candidateEntriesTerm.
  Proof.
    unfold refined_raft_net_invariant_reboot, prevLog_candidateEntriesTerm, reboot.
    simpl. intros.
    eapply candidateEntriesTerm_ext; eauto.
    repeat find_rewrite.
    find_apply_hyp_hyp.
    unfold candidateEntriesTerm in *.
    break_exists_exists.
    update_destruct; auto.
    repeat find_rewrite.
    simpl in *. intuition.
    discriminate.
  Qed.

  Lemma prevLog_candidateEntriesTerm_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      prevLog_candidateEntriesTerm net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply prevLog_candidateEntriesTerm_init.
    - apply prevLog_candidateEntriesTerm_client_request.
    - apply prevLog_candidateEntriesTerm_timeout.
    - apply prevLog_candidateEntriesTerm_append_entries.
    - apply prevLog_candidateEntriesTerm_append_entries_reply.
    - apply prevLog_candidateEntriesTerm_request_vote.
    - apply prevLog_candidateEntriesTerm_request_vote_reply.
    - apply prevLog_candidateEntriesTerm_do_leader.
    - apply prevLog_candidateEntriesTerm_do_generic_server.
    - apply prevLog_candidateEntriesTerm_state_same_packet_subset.
    - apply prevLog_candidateEntriesTerm_reboot.
  Qed.

  Instance plceti : prevLog_candidateEntriesTerm_interface.
  Proof.
    constructor.
    apply prevLog_candidateEntriesTerm_invariant.
  Qed.
End PrevLogCandidateEntriesTerm.
