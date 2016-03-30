Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonTheorems.
Require Import RefinementCommonTheorems.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LeaderLogsPreservedInterface.
Require Import LogsLeaderLogsInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import LeaderLogsCandidateEntriesInterface.
Require Import OneLeaderLogPerTermInterface.
Require Import VotesCorrectInterface.
Require Import CroniesCorrectInterface.

Section LeaderLogsPreserved.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {llli : logs_leaderLogs_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {llcei : leaderLogs_candidate_entries_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.
  
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

  Lemma update_elections_data_requestVoteReply_leaderLogs :
    forall h h' t  st t' ll' r,
      In (t', ll') (leaderLogs (fst st)) ->
      In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; auto.
    simpl in *. intuition.
  Qed.

  Lemma update_elections_data_requestVoteReply_leaderLogs' :
    forall h h' t  st t' ll' r,
      In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)) ->
      In (t', ll') (leaderLogs (fst st))
      \/ (r = true
          /\ t = currentTerm (snd st)
          /\ ll' = log (snd st)
          /\ t' = currentTerm (snd st)
          /\ type (snd st) = Candidate
          /\ wonElection (dedup name_eq_dec (h' :: votesReceived (snd st))) = true).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; auto.
    simpl in *. intuition.
    find_inversion. right.
    unfold handleRequestVoteReply in *.
    repeat break_match; simpl in *; intuition; try congruence;
    break_if; try congruence; do_bool; eauto using le_antisym.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).


  Lemma leaderLogs_preserved_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    repeat find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs';
    intuition; subst; eauto.
    - exfalso.
      match goal with
        | H : In _ ?ll, _ : In (_, ?ll) _ |- _ =>
          eapply leaderLogs_term_sanity_invariant in H
      end; eauto.
      find_eapply_lem_hyp leaderLogs_currentTerm_invariant; eauto.
      repeat find_rewrite. 
      repeat (unfold raft_data in *; simpl in *).
      omega.
    - find_apply_lem_hyp logs_leaderLogs_invariant; auto.
      break_exists. intuition.
      find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
      conclude_using eauto. subst.
      find_eapply_lem_hyp app_in_2; eauto using removeAfterIndex_in.
    - find_apply_lem_hyp logs_leaderLogs_invariant; auto.
      break_exists. intuition.
      find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
      conclude_using eauto. subst.
      find_eapply_lem_hyp app_in_2; eauto using removeAfterIndex_in.
    - match goal with
        | H : In _ ?ll, _ : In (_, ?ll) _ |- _ =>
          eapply leaderLogs_candidate_entries_invariant in H
      end; eauto.
      find_eapply_lem_hyp wonElection_candidateEntries_rvr;
        repeat find_rewrite; eauto using votes_correct_invariant, cronies_correct_invariant.
      intuition.
  Qed.

  Lemma leaderLogs_preserved_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    repeat find_rewrite_lem update_elections_data_appendEntries_leaderLogs;
    intuition; subst; eauto.
  Qed.

  Lemma leaderLogs_preserved_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    repeat find_rewrite_lem update_elections_data_appendEntriesReply_leaderLogs;
    intuition; subst; eauto.
  Qed.

  Lemma leaderLogs_preserved_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    repeat find_rewrite_lem update_elections_data_requestVote_leaderLogs;
    intuition; subst; eauto.
  Qed.

  Lemma leaderLogs_preserved_client_request :
    refined_raft_net_invariant_client_request leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    repeat find_rewrite_lem update_elections_data_client_request_leaderLogs;
    intuition; subst; eauto.
  Qed.

  Lemma leaderLogs_preserved_timeout :
    refined_raft_net_invariant_timeout leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    repeat find_rewrite_lem update_elections_data_timeout_leaderLogs;
    intuition; subst; eauto.
  Qed.

  Lemma leaderLogs_preserved_init :
    refined_raft_net_invariant_init leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *. intuition.
  Qed.

  Lemma leaderLogs_preserved_reboot :
    refined_raft_net_invariant_reboot leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end. 
    repeat find_higher_order_rewrite. subst.
    destruct_update; simpl in *; eauto.
  Qed.

  Lemma leaderLogs_preserved_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma leaderLogs_preserved_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.
    

  Lemma leaderLogs_preserved_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_preserved.
  Proof.
    red. unfold leaderLogs_preserved. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
  Qed.

  Theorem leaderLogs_preserved_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_preserved net.
  Proof.
    intros. apply refined_raft_net_invariant; auto.
    - apply leaderLogs_preserved_init.
    - apply leaderLogs_preserved_client_request.
    - apply leaderLogs_preserved_timeout.
    - apply leaderLogs_preserved_append_entries.
    - apply leaderLogs_preserved_append_entries_reply.
    - apply leaderLogs_preserved_request_vote.
    - apply leaderLogs_preserved_request_vote_reply.
    - apply leaderLogs_preserved_do_leader.
    - apply leaderLogs_preserved_do_generic_server.
    - apply leaderLogs_preserved_state_same_packet_subset.
    - apply leaderLogs_preserved_reboot.
  Qed.
      
  Instance llpi : leaderLogs_preserved_interface.
  split. eauto using leaderLogs_preserved_invariant.
  Defined.
  
End LeaderLogsPreserved.
