Require Import Raft.
Require Import RaftRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import AppendEntriesRequestsCameFromLeadersInterface.
Require Import OneLeaderLogPerTermInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import OneLeaderPerTermInterface.

Require Import AppendEntriesLeaderInterface.

Section AppendEntriesLeader.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Context {aecfli : append_entries_came_from_leaders_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {olpti : one_leader_per_term_interface}.

  Ltac update_destruct :=
    match goal with
    | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
      destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    | [ |- context [ update _ ?x _ ?y ] ] =>
      destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma appendEntries_leader_init :
    refined_raft_net_invariant_init appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_init, appendEntries_leader.
    simpl. intuition.
  Qed.

  Definition type_term_log_monotonic st st' :=
    type st' = Leader ->
    type st = Leader /\
    currentTerm st' = currentTerm st /\
    (forall e, In e (log st) -> In e (log st')).

  Notation appendEntries_leader_predicate ps st :=
    (forall p t lid pli plt es lci e,
      In p ps ->
      pBody p = AppendEntries t lid pli plt es lci ->
      In e es ->
      currentTerm st = t ->
      type st = Leader ->
      In e (log st)).

  Lemma appendEntries_leader_predicate_TTLM_preserved :
    forall ps st st',
      appendEntries_leader_predicate ps st ->
      type_term_log_monotonic st st' ->
      appendEntries_leader_predicate ps st'.
  Proof.
    unfold type_term_log_monotonic.
    intuition.
    repeat find_rewrite.
    eauto.
  Qed.

  Lemma handleClientRequest_TTLM :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold type_term_log_monotonic.
    intros.
    find_copy_apply_lem_hyp handleClientRequest_type.
    find_copy_apply_lem_hyp handleClientRequest_log.
    intuition; try congruence.
    break_exists.
    intuition. subst. repeat find_rewrite. auto with *.
  Qed.

  Lemma appendEntries_leader_client_request :
    refined_raft_net_invariant_client_request appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_client_request, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp. intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleClientRequest_TTLM.
        eauto.
      + eauto.
    - find_apply_lem_hyp handleClientRequest_packets.
      subst. simpl in *. intuition.
  Qed.

  Lemma handleTimeout_TTLM :
    forall h st out st' l,
      handleTimeout h st = (out, st', l) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold type_term_log_monotonic.
    intros.
    find_copy_apply_lem_hyp handleTimeout_type.
    find_apply_lem_hyp handleTimeout_log_same.
    intuition; try congruence.
  Qed.

  Lemma appendEntries_leader_timeout :
    refined_raft_net_invariant_timeout appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_timeout, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleTimeout_TTLM.
        eauto.
      + eauto.
    - do_in_map.
      find_eapply_lem_hyp handleTimeout_packets; eauto.
      subst. exfalso. eauto 10.
  Qed.

  Lemma handleAppendEntries_TTLM :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold type_term_log_monotonic, handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma appendEntries_leader_append_entries :
    refined_raft_net_invariant_append_entries appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_append_entries, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleAppendEntries_TTLM.
        eauto.
      + eauto.
    - find_apply_lem_hyp handleAppendEntries_not_append_entries.
      subst. exfalso. eauto 10.
  Qed.

  Lemma handleAppendEntriesReply_TTLM :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold type_term_log_monotonic, handleAppendEntriesReply, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma appendEntries_leader_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleAppendEntriesReply_TTLM.
        eauto.
      + eauto.
    - find_apply_lem_hyp handleAppendEntriesReply_packets.
      subst. simpl in *. intuition.
  Qed.

  Lemma handleRequestVote_TTLM :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold type_term_log_monotonic, handleRequestVote, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma appendEntries_leader_request_vote :
    refined_raft_net_invariant_request_vote appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_request_vote, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleRequestVote_TTLM.
        eauto.
      + eauto.
    - find_apply_lem_hyp handleRequestVote_no_append_entries.
      subst. exfalso. eauto 10.
  Qed.

(* p0 is AE.
   by AE_came_from_leaders, there is a ll in pre state at (pSrc p0) for p0's term.
   claim I am (pSrc p0).
     I am ascending, so I have ll in post state.
     pSrc p0 ll still is preserved into post state.
     finish with one ll per term.
   thus I had a leaderLog in the pre state.
   this contradicts leaderLogs_currentTerm_sanity_candidate.
*)

  Lemma handleRequestVoteReply_spec' :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      type st' = Follower \/
      st' = st \/
      type st' = Candidate \/
      (type st' = Leader /\
       type st = Candidate /\
       log st' = log st /\
       r = true /\
       t = currentTerm st /\
       wonElection (dedup name_eq_dec (h' :: votesReceived st)) = true /\
       currentTerm st' = currentTerm st).
  Proof.
    unfold handleRequestVoteReply.
    intros.
    repeat break_match; repeat find_inversion; do_bool; subst; simpl; intuition.
  Qed.

  Lemma update_elections_data_RVR_ascending_leaderLog :
    forall h src t1 v st,
      type (snd st) = Candidate ->
      type (handleRequestVoteReply h (snd st) src t1 v) = Leader ->
      exists ll,
        In (currentTerm (snd st), ll) (leaderLogs (update_elections_data_requestVoteReply h src t1 v st)).
  Proof.
    unfold update_elections_data_requestVoteReply, handleRequestVoteReply.
    intros.
    repeat find_rewrite. simpl in *.
    repeat break_match; repeat find_inversion; subst; simpl in *; try congruence; eauto.
  Qed.

  Lemma appendEntries_leader_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply' appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply', appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    find_copy_apply_lem_hyp handleRequestVoteReply_spec'.
    repeat find_higher_order_rewrite.
    update_destruct.
    - rewrite handleRequestVoteReply_same_log.
      intuition; try congruence.
      + repeat find_rewrite.
        eauto using in_middle_insert with *.
      + subst.
        match goal with
        | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] =>
          copy_eapply (append_entries_came_from_leaders_invariant net) H
        end; eauto.
        break_exists.
        assert (pDst p = pSrc p0).
        {
          destruct (name_eq_dec (pDst p) (pSrc p0)); auto.
          find_copy_apply_lem_hyp update_elections_data_RVR_ascending_leaderLog; auto.
          break_exists.
          repeat find_rewrite.
          match goal with
          | [ H : refined_raft_intermediate_reachable ?the_net,
              H': In (?the_t, ?the_ll) (leaderLogs (update_elections_data_requestVoteReply _ _ _ _ _)),
              H'' : In (_, ?the_ll') (leaderLogs (fst _))
              |- _ ] =>
            match the_net with
            | context [ st' ] =>
              apply one_leaderLog_per_term_host_invariant
              with (net0 := the_net) (t := the_t) (ll := the_ll) (ll' := the_ll')
            end
          end; auto; simpl; repeat find_higher_order_rewrite; rewrite_update; simpl; auto.
        }
        exfalso.
        repeat find_rewrite.
        eapply lt_irrefl.
        eapply leaderLogs_currentTerm_sanity_candidate_invariant; [|eauto|]; auto.
    - eauto.
  Qed.

  Lemma doLeader_TTLM :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold doLeader, type_term_log_monotonic.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma doLeader_message_entries :
    forall st h os st' ms m t n pli plt es ci e,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      In e es ->
      currentTerm st = t /\
      type st = Leader /\
      In e (log st).
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    break_match; try solve [find_inversion; simpl in *; intuition].
    break_if; try solve [find_inversion; simpl in *; intuition].
    find_inversion. simpl. do_in_map. subst.
    simpl in *. find_inversion.
    eauto using findGtIndex_in.
  Qed.

  Lemma lifted_one_leader_per_term :
    forall net h h',
      refined_raft_intermediate_reachable net ->
      currentTerm (snd (nwState net h)) = currentTerm (snd (nwState net h')) ->
      type (snd (nwState net h)) = Leader ->
      type (snd (nwState net h')) = Leader ->
      h = h'.
  Proof.
    intros.
    eapply (lift_prop _ one_leader_per_term_invariant _ ltac:(eauto));
      simpl in *; repeat break_match; repeat (find_rewrite; simpl in *);
      auto; simpl in *; repeat find_rewrite; simpl in *; auto.
  Qed.


  Lemma appendEntries_leader_do_leader :
    refined_raft_net_invariant_do_leader appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_do_leader, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using doLeader_TTLM.
        match goal with
        | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] =>
          replace d with (snd (nwState net h)) in * by (rewrite H; auto)
        end.
        eauto.
      + eauto.
    - do_in_map. subst. simpl in *.
      repeat find_higher_order_rewrite.
      find_copy_eapply_lem_hyp (doLeader_message_entries d);
        match goal with
        | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] =>
          replace d with (snd (nwState net h)) in * by (rewrite H; auto)
        end; eauto; break_and.
      update_destruct.
      + erewrite doLeader_same_log; eauto.
      + exfalso. eauto using lifted_one_leader_per_term.
  Qed.

  Lemma doGenericServer_TTLM :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      type_term_log_monotonic st st'.
  Proof.
    unfold type_term_log_monotonic, doGenericServer.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence;
    use_applyEntries_spec; subst; simpl in *; auto.
  Qed.

  Lemma appendEntries_leader_do_generic_server :
    refined_raft_net_invariant_do_generic_server appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, appendEntries_leader.
    simpl.
    intros.
    find_apply_hyp_hyp.
    intuition.
    - repeat find_higher_order_rewrite.
      update_destruct.
      + eapply appendEntries_leader_predicate_TTLM_preserved; eauto using doGenericServer_TTLM.
        match goal with
        | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] =>
          replace d with (snd (nwState net h)) in * by (rewrite H; auto)
        end.
        eauto.
      + eauto.
    - find_apply_lem_hyp doGenericServer_packets. subst. simpl in *. intuition.
  Qed.

  Lemma appendEntries_leader_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, appendEntries_leader.
    simpl. intros.
    repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma appendEntries_leader_reboot :
    refined_raft_net_invariant_reboot appendEntries_leader.
  Proof.
    unfold refined_raft_net_invariant_reboot, appendEntries_leader, reboot.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    update_destruct.
    - discriminate.
    - eauto.
  Qed.

  Lemma appendEntries_leader_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntries_leader net.
  Proof.
    intros.
    apply refined_raft_net_invariant'; auto.
    - apply appendEntries_leader_init.
    - apply refined_raft_net_invariant_client_request'_weak.
      apply appendEntries_leader_client_request.
    - apply refined_raft_net_invariant_timeout'_weak.
      apply appendEntries_leader_timeout.
    - apply refined_raft_net_invariant_append_entries'_weak.
      apply appendEntries_leader_append_entries.
    - apply refined_raft_net_invariant_append_entries_reply'_weak.
      apply appendEntries_leader_append_entries_reply.
    - apply refined_raft_net_invariant_request_vote'_weak.
      apply appendEntries_leader_request_vote.
    - apply appendEntries_leader_request_vote_reply.
    - apply refined_raft_net_invariant_do_leader'_weak.
      apply appendEntries_leader_do_leader.
    - apply refined_raft_net_invariant_do_generic_server'_weak.
      apply appendEntries_leader_do_generic_server.
    - apply appendEntries_leader_state_same_packet_subset.
    - apply refined_raft_net_invariant_reboot'_weak.
      apply appendEntries_leader_reboot.
  Qed.

  Instance appendeli : append_entries_leader_interface.
  Proof.
    split.
    exact appendEntries_leader_invariant.
  Qed.
End AppendEntriesLeader.
