Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import StructTact.Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import RaftUpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import StructTact.StructTactics.

Require Import VotesCorrectInterface.
Require Import VotesLeCurrentTermInterface.

Set Bullet Behavior "Strict Subproofs".

Section VotesCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {vlcti : votes_le_current_term_interface}.

  Ltac split_votes_correct :=
    intros; subst;
    intuition; [ unfold one_vote_per_term in *
               | unfold votes_currentTerm_votedFor_correct in *
               | unfold currentTerm_votedFor_votes_correct in * ];
    cbn [nwState].

  Ltac start_proof :=
    intros;
    match goal with H : forall _, ?f _ = _ |- _ => rewrite H in * end;
    update_destruct; rewrite_update;
    cbn [fst snd] in *; eauto.

  Lemma votes_correct_client_request :
    refined_raft_net_invariant_client_request votes_correct.
  Proof.
    unfold refined_raft_net_invariant_client_request, votes_correct.
    split_votes_correct; start_proof;
    rewrite @votes_update_elections_data_client_request in *;
    find_apply_lem_hyp handleClientRequest_term_votedFor; break_and;
      repeat find_rewrite; eauto.
  Qed.

  Ltac do_le_antisym :=
    match goal with
    | [ H : ?x <= ?y, H' : ?y <= ?x |- _ ] =>
      assert (x = y) by auto using Nat.le_antisymm
    end.

  Lemma votes_correct_timeout :
    refined_raft_net_invariant_timeout votes_correct.
  Proof.
    unfold refined_raft_net_invariant_timeout, votes_correct.
    split_votes_correct; start_proof.
    - find_eapply_lem_hyp votes_update_elections_data_timeout_votedFor; eauto.
      find_eapply_lem_hyp votes_update_elections_data_timeout_votedFor; eauto.
      intuition.
      + eauto.
      + find_apply_lem_hyp votes_le_current_term_invariant; auto; simpl in *; omega.
      + find_apply_lem_hyp votes_le_current_term_invariant; auto; simpl in *; omega.
      + congruence.
    - find_eapply_lem_hyp votes_update_elections_data_timeout_votedFor; eauto.
      intuition. subst.
      find_copy_apply_lem_hyp votes_le_current_term_invariant; auto.
      find_copy_apply_lem_hyp handleTimeout_currentTerm.
      do_le_antisym.
      erewrite handleTimeout_same_term_votedFor_preserved by eauto.
      eauto.
    - eapply update_elections_data_timeout_votes_intro_new; intuition eauto.
  Qed.

  Lemma votes_correct_append_entries :
    refined_raft_net_invariant_append_entries votes_correct.
  Proof.
    unfold refined_raft_net_invariant_append_entries, votes_correct.
    split_votes_correct; start_proof; rewrite @votes_same_append_entries in *.
    - eauto.
    - find_copy_apply_lem_hyp votes_le_current_term_invariant; auto.
      find_copy_apply_lem_hyp handleAppendEntries_currentTerm.
      subst.
      do_le_antisym.
      erewrite handleAppendEntries_same_term_votedFor_preserved by eauto.
      eauto.
    - find_copy_eapply_lem_hyp handleAppendEntries_term_votedFor; eauto.
      break_and.
      subst. eauto using eq_trans.
  Qed.

  Lemma votes_correct_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votes_correct.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, votes_correct.
    split_votes_correct; start_proof.
    - find_copy_apply_lem_hyp votes_le_current_term_invariant; auto.
      find_copy_apply_lem_hyp handleAppendEntriesReply_currentTerm.
      subst.
      do_le_antisym.
      erewrite handleAppendEntriesReply_same_term_votedFor_preserved by eauto.
      eauto.
    - find_copy_eapply_lem_hyp handleAppendEntriesReply_term_votedFor; eauto.
      break_and. subst.
      eauto using eq_trans.
  Qed.

  Lemma votes_correct_request_vote :
    refined_raft_net_invariant_request_vote votes_correct.
  Proof.
    unfold refined_raft_net_invariant_request_vote, votes_correct.
    split_votes_correct; start_proof.
    - find_eapply_lem_hyp votes_update_elections_data_request_vote; eauto.
      find_eapply_lem_hyp votes_update_elections_data_request_vote; eauto.
      intuition; [eauto | | | congruence]; subst;
        find_copy_apply_lem_hyp votes_le_current_term_invariant; auto;
        find_copy_apply_lem_hyp handleRequestVote_currentTerm;
        do_le_antisym;
        match goal with
        | [ H : votes_currentTerm_votedFor_correct _, H' : In _ _  |- _ ] =>
          apply H in H'; conclude_using congruence
        end;
        find_apply_lem_hyp handleRequestVote_votedFor; auto;
        intuition congruence.
    - find_eapply_lem_hyp votes_update_elections_data_request_vote; eauto.
      intuition.
      subst.
      find_copy_apply_lem_hyp votes_le_current_term_invariant; auto.
      find_copy_apply_lem_hyp handleRequestVote_currentTerm.
      do_le_antisym.
      find_apply_hyp_hyp.
      find_copy_apply_lem_hyp handleRequestVote_currentTerm_votedFor.
      intuition; try omega; try congruence.
    - subst.
      find_copy_apply_lem_hyp handleRequestVote_currentTerm_votedFor.
      repeat find_rewrite.
      intuition.
      + eauto using votes_update_elections_data_request_vote_intro.
      + eauto using votes_update_elections_data_request_vote_intro.
      + eauto using votes_update_elections_data_request_vote_intro_old.
  Qed.

  Lemma votes_correct_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votes_correct.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, votes_correct.
    split_votes_correct; start_proof.
    - erewrite @votes_update_elections_data_request_vote_reply_eq in * by auto.
      eauto.
    - erewrite @votes_update_elections_data_request_vote_reply_eq in * by auto.
      find_copy_apply_lem_hyp votes_le_current_term_invariant; auto.
      subst.
      match goal with
      | [ H : context [currentTerm ?x] |- _ ] =>
        remember x as st'' eqn:Hst'';
        apply eq_sym in Hst''
      end.
      find_copy_apply_lem_hyp handleRequestVoteReply_term_votedFor_cases.
      intuition; try omega.
      repeat find_rewrite. eauto.
    - erewrite @votes_update_elections_data_request_vote_reply_eq in * by auto.
      find_copy_eapply_lem_hyp handleRequestVoteReply_term_votedFor; eauto.
      intuition.
      repeat find_rewrite. eauto.
  Qed.

  Lemma votes_correct_do_leader :
    refined_raft_net_invariant_do_leader votes_correct.
  Proof.
    unfold refined_raft_net_invariant_do_leader, votes_correct.
    intros.
    match goal with H : nwState _ _ = _ |- _ =>
      assert (gd = fst (nwState net h) /\
              d = snd (nwState net h)) by (intuition; find_rewrite; reflexivity);
        clear H
    end.
    split_votes_correct; start_proof; subst.
    - eauto.
    - find_apply_lem_hyp doLeader_term_votedFor. break_and.
      repeat find_rewrite. eauto.
    - find_apply_lem_hyp doLeader_term_votedFor. break_and.
      repeat find_rewrite. eauto.
  Qed.

  Lemma votes_correct_do_generic_server :
    refined_raft_net_invariant_do_generic_server votes_correct.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, votes_correct.
    intros.
    match goal with H : nwState _ _ = _ |- _ =>
      assert (gd = fst (nwState net h) /\
              d = snd (nwState net h)) by (intuition; find_rewrite; reflexivity);
        clear H
    end.
    split_votes_correct; start_proof; subst.
    - eauto.
    - find_apply_lem_hyp doGenericServer_log_type_term_votesReceived. break_and.
      repeat find_rewrite. eauto.
    - find_apply_lem_hyp doGenericServer_log_type_term_votesReceived. break_and.
      repeat find_rewrite. eauto.
  Qed.

  Lemma votes_correct_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votes_correct.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, votes_correct.
    split_votes_correct;
      intros; repeat find_reverse_higher_order_rewrite; eauto.
  Qed.

  Lemma votes_correct_reboot :
    refined_raft_net_invariant_reboot votes_correct.
  Proof.
    unfold refined_raft_net_invariant_reboot, votes_correct, reboot.
    intros.
    match goal with H : nwState _ _ = _ |- _ =>
      assert (gd = fst (nwState net h) /\
              d = snd (nwState net h)) by (intuition; repeat find_rewrite; reflexivity);
        clear H
    end.
    split_votes_correct; start_proof;
      subst; simpl in *; eauto.
  Qed.

  Theorem votes_correct_init :
    refined_raft_net_invariant_init votes_correct.
  Proof.
    unfold refined_raft_net_invariant_init, votes_correct.
    split_votes_correct; simpl in *; intuition; discriminate.
  Qed.

  Theorem votes_correct_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      votes_correct net.
  Proof.
    intros.
    eapply refined_raft_net_invariant; eauto.
    - apply votes_correct_init.
    - apply votes_correct_client_request.
    - apply votes_correct_timeout.
    - apply votes_correct_append_entries.
    - apply votes_correct_append_entries_reply.
    - apply votes_correct_request_vote.
    - apply votes_correct_request_vote_reply.
    - apply votes_correct_do_leader.
    - apply votes_correct_do_generic_server.
    - apply votes_correct_state_same_packet_subset.
    - apply votes_correct_reboot.
  Qed.

  Instance vci : votes_correct_interface.
  Proof.
    split.
    auto using votes_correct_invariant.
  Qed.
End VotesCorrect.
