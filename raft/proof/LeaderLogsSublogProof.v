Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LeaderSublogInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import EveryEntryWasCreatedInterface.
Require Import LeaderLogsCandidateEntriesInterface.

Require Import CroniesCorrectInterface.
Require Import VotesCorrectInterface.

Require Import RefinementCommonTheorems.

Require Import LeaderLogsSublogInterface.

Section LeaderLogsSublog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {eewci : every_entry_was_created_interface}.
  Context {llcei : leaderLogs_candidate_entries_interface}.

  Context {cci : cronies_correct_interface}.
  Context {vci : votes_correct_interface}.

  Theorem leaderLogs_sublog_init :
    refined_raft_net_invariant_init leaderLogs_sublog.
  Proof.
    unfold refined_raft_net_invariant_init, leaderLogs_sublog.
    simpl. intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst_max; rewrite_update; simpl in *
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst_max; rewrite_update; simpl in *
    end.

  Ltac start :=
    repeat match goal with
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := fst) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := snd) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := leaderLogs) in H
           end;
  rewrite update_fun_comm with (f := snd);
  simpl in *;
  match goal with
    | [ H : context [ type ] |- _ ] =>
      rewrite update_fun_comm in H;
        rewrite update_nop_ext' in H by auto
  end;
  match goal with
    | [ H : context [ currentTerm ] |- _ ] =>
      rewrite update_fun_comm in H;
        rewrite update_nop_ext' in H by auto
  end.

  Theorem leaderLogs_sublog_client_request :
    refined_raft_net_invariant_client_request leaderLogs_sublog.
  Proof.
    unfold refined_raft_net_invariant_client_request, leaderLogs_sublog.
    intuition.
    simpl in *.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleClientRequest_type. intuition.
    start.
    find_rewrite_lem update_elections_data_client_request_leaderLogs.
    find_erewrite_lem update_nop_ext' .
    update_destruct.
    - destruct (log d) using (handleClientRequest_log_ind $(eauto)$).
      + eauto.
      + simpl. right. eauto.
    - eauto.
  Qed.

  Theorem leaderLogs_sublog_timeout :
    refined_raft_net_invariant_timeout leaderLogs_sublog.
  Proof.
    unfold refined_raft_net_invariant_timeout, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleTimeout_type.
    intuition.
    - start.
      find_rewrite_lem update_elections_data_timeout_leaderLogs.
      find_erewrite_lem update_nop_ext' .
      update_destruct; eauto.
      erewrite handleTimeout_log_same by eauto; eauto.
    - repeat update_destruct; try congruence.
      + find_rewrite_lem update_elections_data_timeout_leaderLogs.
        eauto.
      + eauto.
  Qed.

  Lemma handleAppendEntries_leader :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      type st' = Leader ->
      log st' = log st.
  Proof.
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; discriminate.
  Qed.

  Theorem leaderLogs_sublog_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_sublog.
  Proof.
    unfold refined_raft_net_invariant_append_entries, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleAppendEntries_type.
    intuition.
    - start.
      find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
      find_erewrite_lem update_nop_ext'.
      update_destruct; eauto.
      erewrite handleAppendEntries_leader by (eauto; congruence).
      eauto.
    - repeat update_destruct; try congruence.
      + find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
        eauto.
      + eauto.
  Qed.

  Theorem leaderLogs_sublog_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_sublog.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_type.
    intuition.
    - start.
      find_erewrite_lem update_nop_ext'.
      update_destruct; eauto.
      erewrite handleAppendEntriesReply_same_log by eauto.
      eauto.
    - repeat update_destruct; try congruence; eauto.
  Qed.

  Theorem leaderLogs_sublog_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_sublog.
  Proof.
    unfold refined_raft_net_invariant_request_vote, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleRequestVote_type.
    intuition.
    - start.
      find_rewrite_lem leaderLogs_update_elections_data_requestVote.
      find_erewrite_lem update_nop_ext'.
      update_destruct; eauto.
      erewrite handleRequestVote_same_log by eauto.
      eauto.
    - repeat update_destruct; try congruence.
      + find_rewrite_lem leaderLogs_update_elections_data_requestVote.
        eauto.
      + eauto.
  Qed.

  Lemma lifted_leader_sublog_host :
    forall net leader h e,
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net leader)) = Leader ->
      In e (log (snd (nwState net h))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).
  Proof.
    intros.
    pose proof (lift_prop _ leader_sublog_invariant_invariant).
    find_apply_hyp_hyp.
    match goal with H : forall _ , _ |- _ => clear H end.
    unfold leader_sublog_invariant, leader_sublog_host_invariant in *.
    break_and.
    do 3 find_insterU.
    repeat find_rewrite_lem deghost_spec.
    eauto.
  Qed.

  Lemma handleRequestVoteReply_RVR_spec :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      st' = st \/
      (type st' = Follower /\
       currentTerm st' = t /\
       log st' = log st) \/
      (currentTerm st' = currentTerm st /\
       log st' = log st /\
       ((type st = Candidate /\ type st' = Leader /\ r = true /\ currentTerm st = t /\
         wonElection (dedup name_eq_dec (h' :: votesReceived st)) = true) \/ type st' = type st)).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try right; congruence.
  Qed.

  Lemma contradict_leaderLogs_term_sanity :
    forall net h t ll e,
      refined_raft_intermediate_reachable net ->
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In e ll ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      False.
  Proof.
    intros.
    find_copy_eapply_lem_hyp leaderLogs_term_sanity_invariant; eauto.
    find_eapply_lem_hyp leaderLogs_currentTerm_invariant; eauto.
    omega.
  Qed.

  Arguments dedup : simpl never.

  Lemma leaderLogs_candidate_entries_rvr :
    forall net,
      leaderLogs_candidateEntries (nwState net) ->
      votes_correct net ->
      cronies_correct net ->
      forall p h t ll e,
        In (t, ll) (leaderLogs (fst (nwState net h))) ->
        In e ll ->
        In p (nwPackets net) ->
        pBody p = RequestVoteReply (eTerm e) true ->
        currentTerm (snd (nwState net (pDst p))) = eTerm e ->
        wonElection (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p))))) = true ->
        type (snd (nwState net (pDst p))) <> Candidate.
  Proof.
    intros.
    eapply_prop_hyp leaderLogs_candidateEntries In; eauto.
    eapply wonElection_candidateEntries_rvr; auto. eauto. auto.  auto.
  Qed.

  Theorem leaderLogs_sublog_request_vote_reply :
    forall xs p ys net st' ps' gd d t v,
      handleRequestVoteReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t v = d ->
      gd = update_elections_data_requestVoteReply (pDst p) (pSrc p) t v (nwState net (pDst p)) ->
      pBody p = RequestVoteReply t v ->
      leaderLogs_sublog net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      leaderLogs_sublog (mkNetwork ps' st').
  Proof.
    unfold leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleRequestVoteReply_RVR_spec.
    intuition.
    - subst. repeat find_rewrite.
      repeat update_destruct; eauto;
      find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition eauto;
      unfold raft_data in *; congruence.
    - repeat update_destruct; try congruence.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition eauto.
        subst_max. repeat find_rewrite. discriminate.
      + eauto.
    - repeat update_destruct.
      + repeat find_rewrite.
        find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * exfalso. eauto using contradict_leaderLogs_term_sanity.
        * subst. unfold raft_data in *. repeat find_rewrite. auto.
      + repeat find_rewrite.
        exfalso.
        eapply leaderLogs_candidate_entries_rvr; eauto;
          eauto using leaderLogs_candidate_entries_invariant,
                      votes_correct_invariant,
                      cronies_correct_invariant.
        congruence.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * eauto.
        * subst. unfold raft_data in *. repeat find_rewrite.
          eapply lifted_leader_sublog_host; eauto.
      + eauto.
    - repeat update_destruct.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * repeat find_rewrite. eauto.
        * subst. unfold raft_data in *. repeat find_rewrite. auto.
      + repeat find_rewrite. eauto.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * repeat find_rewrite. eauto.
        * subst. unfold raft_data in *. repeat find_rewrite. discriminate.
      + eauto.
  Qed.

  Theorem leaderLogs_sublog_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_sublog.
  Admitted.

  Theorem leaderLogs_sublog_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_sublog.
  Admitted.

  Theorem leaderLogs_sublog_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_sublog.
  Admitted.

  Theorem leaderLogs_sublog_reboot :
    refined_raft_net_invariant_reboot leaderLogs_sublog.
  Admitted.

  Theorem leaderLogs_sublog_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_sublog net.
  Proof.
    intros.
    eapply refined_raft_net_invariant; eauto.
    - apply leaderLogs_sublog_init.
    - apply leaderLogs_sublog_client_request.
    - apply leaderLogs_sublog_timeout.
    - apply leaderLogs_sublog_append_entries.
    - apply leaderLogs_sublog_append_entries_reply.
    - apply leaderLogs_sublog_request_vote.
    - unfold refined_raft_net_invariant_request_vote_reply.
      intros.
      eapply leaderLogs_sublog_request_vote_reply; eauto.
      eapply RRIR_handleMessage; eauto.
      + repeat find_rewrite. simpl. eauto.
      + intros. repeat find_higher_order_rewrite.
        simpl. repeat f_equal. auto.
    - apply leaderLogs_sublog_do_leader.
    - apply leaderLogs_sublog_do_generic_server.
    - apply leaderLogs_sublog_state_same_packet_subset.
    - apply leaderLogs_sublog_reboot.
  Qed.

  Instance llsli : leaderLogs_sublog_interface.
  Proof.
    split.
    exact leaderLogs_sublog_invariant.
  Qed.
End LeaderLogsSublog.
