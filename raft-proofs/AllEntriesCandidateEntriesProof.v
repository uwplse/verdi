Require Import Raft.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import RaftRefinementInterface.
Require Import CommonTheorems.
Require Import RefinementCommonTheorems.

Require Import CandidateEntriesInterface.
Require Import CroniesCorrectInterface.
Require Import CroniesTermInterface.
Require Import AllEntriesTermSanityInterface.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import AllEntriesCandidateEntriesInterface.

Section AllEntriesCandidateEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {cci : cronies_correct_interface}.
  Context {cti : cronies_term_interface}.
  Context {cei : candidate_entries_interface}.
  Context {lltsi : allEntries_term_sanity_interface}.

  Ltac start :=
    red; unfold allEntries_candidateEntries; simpl; intros.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).
  
  Lemma allEntries_candidateEntries_init :
    refined_raft_net_invariant_init allEntries_candidateEntries.
  Proof.
    start. contradiction.
  Qed.

  Lemma allEntries_candidateEntries_client_request :
    refined_raft_net_invariant_client_request allEntries_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_copy_apply_lem_hyp update_elections_data_client_request_allEntries.
        intuition;
        repeat find_rewrite; eauto.
      + find_apply_hyp_hyp.
        unfold candidateEntries in *.
        break_exists_exists.
        destruct_update; simpl in *; eauto.
        erewrite update_elections_data_client_request_cronies; eauto.
        intuition.
        find_apply_lem_hyp handleClientRequest_type.
        intuition. repeat find_rewrite. eauto.
      + break_exists. intuition.
        repeat find_rewrite. simpl in *. intuition.
        * find_inversion.
          exists h0. rewrite_update.
          simpl.
          find_copy_apply_lem_hyp handleClientRequest_type.
          break_and; repeat find_rewrite; intuition; try congruence.
          erewrite update_elections_data_client_request_cronies; eauto.
          eapply won_election_cronies; repeat find_rewrite;
          eauto using cronies_correct_invariant.
        * find_apply_hyp_hyp.
          unfold candidateEntries in *.
          break_exists_exists.
          destruct_update; simpl in *; eauto.
          erewrite update_elections_data_client_request_cronies; eauto.
          intuition.
          find_apply_lem_hyp handleClientRequest_type.
          intuition. repeat find_rewrite. eauto.
    - find_apply_hyp_hyp.
      unfold candidateEntries in *.
      break_exists_exists.
      destruct_update; simpl in *; eauto.
      erewrite update_elections_data_client_request_cronies; eauto.
      intuition.
      find_apply_lem_hyp handleClientRequest_type.
      intuition. repeat find_rewrite. eauto.
  Qed.

  Lemma allEntries_candidateEntries_timeout :
    refined_raft_net_invariant_timeout allEntries_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { destruct_update; simpl in *.
      - find_rewrite_lem update_elections_data_timeout_allEntries. eauto.
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

  Lemma allEntries_candidateEntries_append_entries :
    refined_raft_net_invariant_append_entries allEntries_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    destruct_update.
    - simpl in *.
      find_eapply_lem_hyp update_elections_data_appendEntries_allEntries_term'; eauto.
      intuition.
      + find_apply_hyp_hyp.
        unfold candidateEntries in *. break_exists_exists.
        destruct_update; [|auto].
        simpl. subst. rewrite update_elections_data_appendEntries_cronies.
        find_copy_apply_lem_hyp handleAppendEntries_type_term.
        intuition; repeat find_rewrite; auto; congruence.
      + subst.
        find_eapply_lem_hyp candidate_entries_invariant; eauto.
        unfold candidateEntries in *.
        break_exists_exists.
        destruct_update; [|auto].
        simpl. subst. rewrite update_elections_data_appendEntries_cronies.
        find_copy_apply_lem_hyp handleAppendEntries_type_term.
        intuition; repeat find_rewrite; auto; congruence.
    - find_apply_hyp_hyp.
        unfold candidateEntries in *. break_exists_exists.
        destruct_update; [|auto].
        simpl. subst. rewrite update_elections_data_appendEntries_cronies.
        find_copy_apply_lem_hyp handleAppendEntries_type_term.
        intuition; repeat find_rewrite; auto; congruence.
  Qed.

  Lemma allEntries_candidateEntries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { destruct_update; eauto. }
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

  Lemma allEntries_candidateEntries_request_vote :
    refined_raft_net_invariant_request_vote allEntries_candidateEntries.
  Proof.
    start.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { destruct_update; simpl in *.
      - find_rewrite_lem update_elections_data_requestVote_allEntries. eauto.
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

  Lemma allEntries_candidateEntries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_candidateEntries.
  Proof.
    start.
    intro_refined_invariant candidate_entries_invariant.
    eapply candidateEntries_ext; eauto.
    subst.
    repeat find_higher_order_rewrite.
    find_rewrite_lem update_fun_comm. simpl in *.
    destruct_update.
    - find_rewrite_lem update_elections_data_requestVoteReply_allEntries; eauto.
      find_apply_hyp_hyp.
      eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
    - eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
  Qed.

  Lemma allEntries_candidateEntries_do_leader :
    refined_raft_net_invariant_do_leader allEntries_candidateEntries.
  Proof.
    start.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    eapply candidateEntries_ext; eauto.
    find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { destruct_update; simpl in *; eauto. }
    unfold candidateEntries in *.
    find_apply_lem_hyp doLeader_st.
    intuition.
    break_exists_exists.
    destruct_update; simpl in *; repeat find_rewrite; auto.
  Qed.

  Lemma allEntries_candidateEntries_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_candidateEntries.
  Proof.
    start.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    eapply candidateEntries_ext; eauto.
    find_higher_order_rewrite.
    assert (candidateEntries e (nwState net)).
    { destruct_update; simpl in *.
      - assert (In (t, e) (allEntries (fst (nwState net h0)))) by (repeat find_rewrite; eauto). eauto.
      - eauto. }
    unfold candidateEntries in *.
    find_apply_lem_hyp doGenericServer_type.
    intuition.
    break_exists_exists.
    destruct_update; simpl in *; repeat find_rewrite; auto.
  Qed.

  Lemma allEntries_candidateEntries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_candidateEntries.
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

  Lemma allEntries_candidateEntries_reboot :
    refined_raft_net_invariant_reboot allEntries_candidateEntries.
  Proof.
    start.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    eapply candidateEntries_ext; eauto.
    repeat find_higher_order_rewrite.
    unfold candidateEntries in *.
    destruct_update; simpl in *;
    find_apply_hyp_hyp; break_exists_exists;
    destruct_update; simpl in *; intuition;
    congruence.
  Qed.

  Lemma allEntries_candidateEntries_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      allEntries_candidateEntries net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply allEntries_candidateEntries_init.
    - apply allEntries_candidateEntries_client_request.
    - apply allEntries_candidateEntries_timeout.
    - apply allEntries_candidateEntries_append_entries.
    - apply allEntries_candidateEntries_append_entries_reply.
    - apply allEntries_candidateEntries_request_vote.
    - apply allEntries_candidateEntries_request_vote_reply.
    - apply allEntries_candidateEntries_do_leader.
    - apply allEntries_candidateEntries_do_generic_server.
    - apply allEntries_candidateEntries_state_same_packet_subset.
    - apply allEntries_candidateEntries_reboot.
  Qed.


  Instance aecei : allEntries_candidate_entries_interface.
  Proof.
    constructor. exact allEntries_candidateEntries_invariant.
  Qed.
End AllEntriesCandidateEntries.
