Require Import Raft.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import RefinementCommonDefinitions.
Require Import RefinementCommonTheorems.

Require Import CandidateEntriesInterface.
Require Import CroniesCorrectInterface.
Require Import CroniesTermInterface.
Require Import LeaderLogsTermSanityInterface.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import LeaderLogsCandidateEntriesInterface.

Section CandidateEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {cci : cronies_correct_interface}.
  Context {cti : cronies_term_interface}.
  Context {cei : candidate_entries_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac start :=
    red; unfold leaderLogs_candidateEntries; simpl; intros.

  Lemma leaderLogs_candidateEntries_init :
    refined_raft_net_invariant_init leaderLogs_candidateEntries.
  Proof.
    start. contradiction.
  Qed.

  Lemma leaderLogs_candidateEntries_client_request :
    refined_raft_net_invariant_client_request leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update; simpl in *.
      - find_rewrite_lem update_elections_data_client_request_leaderLogs. eauto.
      - eauto. }
    eapply candidateEntries_same.
    - eauto.
    - intros. update_destruct; rewrite_update; [|auto].
      simpl. subst. eauto using update_elections_data_client_request_cronies.
    - intros. update_destruct; rewrite_update; [|auto].
      simpl. subst. find_apply_lem_hyp handleClientRequest_type. intuition.
    - intros. update_destruct; rewrite_update; [|auto].
      simpl. subst. find_apply_lem_hyp handleClientRequest_type. intuition.
  Qed.

  Lemma leaderLogs_candidateEntries_timeout :
    refined_raft_net_invariant_timeout leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update; simpl in *.
      - find_rewrite_lem update_elections_data_timeout_leaderLogs. eauto.
      - eauto. }
    unfold candidateEntries in *.
    break_exists; break_and.
    exists x.
    update_destruct; rewrite_update; simpl in *; [|auto].
    subst. split.
    - assert (H100 := update_elections_data_timeout_cronies x (nwState net x) (eTerm e)).
      intuition.
      + find_rewrite. auto.
      + exfalso.
        find_apply_lem_hyp wonElection_exists_voter.
        break_exists.
        find_apply_lem_hyp in_dedup_was_in.
        intro_refined_invariant cronies_term_invariant.
        eapply_prop_hyp cronies_term In.
        simpl in *.
        omega.
    - find_apply_lem_hyp handleTimeout_type_strong.
      break_or_hyp; break_and.
      + repeat find_rewrite. auto.
      + intros. find_rewrite.
        exfalso.
        find_apply_lem_hyp wonElection_exists_voter.
        break_exists.
        find_apply_lem_hyp in_dedup_was_in.
        intro_refined_invariant cronies_term_invariant.
        eapply_prop_hyp cronies_term In.
        simpl in *.
        omega.
  Qed.

  Lemma leaderLogs_candidateEntries_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    update_destruct; rewrite_update.
    - simpl in *.
      find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
      assert (candidateEntries e (nwState net)) by eauto.
      unfold candidateEntries in *.
      break_exists. break_and.
      exists x.
      update_destruct; rewrite_update; [|auto].
      simpl. subst. rewrite update_elections_data_appendEntries_cronies.
      split; [auto|].
      find_apply_lem_hyp handleAppendEntries_type_term.
      break_or_hyp; break_and.
      * repeat find_rewrite. auto.
      * unfold not. intros. find_rewrite. discriminate.
    - assert (candidateEntries e (nwState net)) by eauto.
      unfold candidateEntries in *.
      break_exists. break_and.
      exists x.
      update_destruct; rewrite_update; [|auto].
      simpl. subst. rewrite update_elections_data_appendEntries_cronies.
      split; [auto|].
      find_apply_lem_hyp handleAppendEntries_type_term.
      break_or_hyp; break_and.
      * repeat find_rewrite. auto.
      * unfold not. intros. find_rewrite. discriminate.
  Qed.

  Lemma leaderLogs_candidateEntries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update; eauto. }
    unfold candidateEntries in *.
    break_exists. break_and.
    exists x.
    update_destruct; rewrite_update; simpl; [|auto].
    subst. split; [auto|].
    find_apply_lem_hyp handleAppendEntriesReply_type_term.
    break_or_hyp; break_and.
    - repeat find_rewrite. auto.
    - unfold not. intros. find_rewrite. discriminate.
  Qed.

  Lemma leaderLogs_candidateEntries_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update; simpl in *.
      - find_rewrite_lem leaderLogs_update_elections_data_requestVote. eauto.
      - eauto. }
    unfold candidateEntries in *.
    break_exists. break_and.
    exists x.
    update_destruct; rewrite_update; simpl; [|auto].
    subst. split.
    - rewrite update_elections_data_requestVote_cronies. auto.
    - find_apply_lem_hyp handleRequestVote_type_term.
      break_or_hyp; break_and.
      + repeat find_rewrite. auto.
      + unfold not. intros. find_rewrite. discriminate.
  Qed.

  Lemma leaderLogs_candidateEntries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_candidateEntries.
  Proof.
    start.
    intro_refined_invariant candidate_entries_invariant.
    eapply candidateEntries_ext; eauto.
    subst.
    repeat find_higher_order_rewrite.
    find_rewrite_lem update_fun_comm. simpl in *.
    update_destruct; rewrite_update.
    - find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
      intuition.
      + eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
      + subst. find_erewrite_lem handleRequestVoteReply_log.
        eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
    - eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
  Qed.

  Lemma leaderLogs_candidateEntries_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update; simpl in *.
      - assert (In (t, ll) (leaderLogs (fst (nwState net h)))) by (repeat find_rewrite; eauto). eauto.
      - eauto. }
    unfold candidateEntries in *.
    break_exists; break_and.
    exists x.
    update_destruct; rewrite_update; [|auto].
    simpl. split.
    - assert (gd = fst (nwState net h)). { repeat find_rewrite. simpl. auto. }
      subst. auto.
    - find_apply_lem_hyp doLeader_type.
      break_and. find_rewrite. repeat find_rewrite.
      auto.
  Qed.

  Lemma leaderLogs_candidateEntries_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update; simpl in *.
      - assert (In (t, ll) (leaderLogs (fst (nwState net h)))) by (repeat find_rewrite; eauto). eauto.
      - eauto. }
    unfold candidateEntries in *.
    break_exists; break_and.
    exists x.
    update_destruct; rewrite_update; [|auto].
    simpl. split.
    - assert (gd = fst (nwState net h)). { repeat find_rewrite. simpl. auto. }
      subst. auto.
    - find_apply_lem_hyp doGenericServer_type.
      break_and. find_rewrite. repeat find_rewrite.
      auto.
  Qed.

  Lemma leaderLogs_candidateEntries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_reverse_higher_order_rewrite.
    assert (candidateEntries e (nwState net)) by eauto.
    unfold candidateEntries in *.
    break_exists. break_and.
    exists x.
    repeat find_reverse_higher_order_rewrite. auto.
  Qed.

  Lemma leaderLogs_candidateEntries_reboot :
    refined_raft_net_invariant_reboot leaderLogs_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { update_destruct; rewrite_update.
      - assert (gd = fst (nwState net h)). { repeat find_rewrite. simpl. auto. }
        subst. eauto.
      - eauto. }
    unfold candidateEntries in *.
    break_exists; break_and.
    exists x.
    update_destruct; rewrite_update; [|auto].
    simpl. split.
    - assert (gd = fst (nwState net h)). { repeat find_rewrite. simpl. auto. }
      subst. auto.
    - unfold not. intros. subst. unfold reboot in *. simpl in *. discriminate.
  Qed.

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
  Proof.
    constructor. exact leaderLogs_candidateEntries_invariant.
  Qed.
End CandidateEntriesInterface.
