Require Import GhostSimulations.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import VotesCorrectInterface.
Require Import CroniesCorrectInterface.

Require Import CommonTheorems.
Require Import RefinementCommonDefinitions.

Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section CommonTheorems.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {cci : cronies_correct_interface}.
  Context {vci : votes_correct_interface}.

  Lemma candidateEntries_wonElection :
    forall (net : network (params := raft_refined_multi_params))  e h,
      one_vote_per_term net ->
      cronies_votes net ->
      votes_received_cronies net ->
      candidateEntries e (nwState net) ->
      currentTerm (snd (nwState net h)) = eTerm e ->
      wonElection (dedup name_eq_dec (votesReceived (snd (nwState net h)))) = true ->
      type (snd (nwState net h)) <> Candidate.
  Proof.
    intros.
    unfold candidateEntries in *. break_exists. break_and.
    repeat match goal with
             | [ H : _ |- _ ] => rewrite deghost_spec in H
           end.
    intro.
    assert (x = h).
    {
      match goal with
        | H : wonElection _ = _ |- _ =>
          eapply wonElection_one_in_common in H; [|clear H; eauto]
      end.
      break_exists. break_and.

      eapply_prop one_vote_per_term;
        try solve [eapply_prop cronies_votes; eauto].
      eapply_prop cronies_votes.
      repeat find_reverse_rewrite.
      eapply_prop votes_received_cronies; auto.
    }
    subst.
    concludes.
    contradiction.
  Qed.

  Lemma wonElection_candidateEntries_rvr :
    forall (net : network (params := raft_refined_multi_params)) p e,
      votes_correct net ->
      cronies_correct net ->
      candidateEntries e (nwState net) ->
      In p (nwPackets net) ->
      pBody p = RequestVoteReply (eTerm e) true ->
      currentTerm (snd (nwState net (pDst p))) = eTerm e ->
      wonElection (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p))))) = true ->
      type (snd (nwState net (pDst p))) <> Candidate.
  Proof.
    unfold votes_correct, cronies_correct.
    intros. break_and.

    match goal with
      | [ H : context [ votes_nw ], H' : context [ pBody ] |- _ ] =>
        eapply H in H'
    end.

    unfold candidateEntries in *. break_exists. break_and.
    match goal with
      | H : wonElection _ = _ |- _ =>
        eapply wonElection_one_in_common in H; [|clear H; eauto]
    end.
    break_exists.
    break_and.
    simpl in *.
    intuition.
    - subst.
      apply_prop_hyp cronies_votes In.
      assert (x = pDst p) by (eapply_prop one_vote_per_term; eauto).
      subst. concludes. contradiction.
    - apply_prop_hyp votes_received_cronies In. concludes.
      apply_prop_hyp cronies_votes In.
      apply_prop_hyp cronies_votes In.
      unfold raft_data in *. unfold raft_refined_base_params, raft_refined_multi_params in *.
      simpl in *.
      repeat find_reverse_rewrite.
      assert (x = pDst p) by (eapply_prop one_vote_per_term; eauto).
      subst.
      repeat concludes. contradiction.
  Qed.

    Lemma candidateEntries_ext :
    forall e sigma sigma',
      (forall h, sigma' h = sigma h) ->
      candidateEntries e sigma ->
      candidateEntries e sigma'.
  Proof.
    unfold candidateEntries.
    intuition.
    break_exists_exists.
    intuition;
    repeat find_higher_order_rewrite; auto.
  Qed.

  Lemma candidateEntries_same :
    forall (st st' : name -> _) e,
      candidateEntries e st ->
      (forall h, cronies (fst (st' h)) = cronies (fst (st h))) ->
      (forall h, currentTerm (snd (st' h)) = currentTerm (snd (st h))) ->
      (forall h, type (snd (st' h)) = type (snd (st h))) ->
      candidateEntries e st'.
  Proof.
    unfold candidateEntries.
    intuition. break_exists. break_and.
    eexists.
    repeat find_higher_order_rewrite.
    eauto.
  Qed.

  Lemma won_election_cronies :
    forall net h,
      cronies_correct net ->
      type (snd (nwState net h)) = Leader ->
      wonElection (dedup name_eq_dec (cronies (fst (nwState net h))
                                              (currentTerm (snd (nwState net h))))) = true.
  Proof.
    intros.
    unfold cronies_correct in *; intuition.
    eapply wonElection_no_dup_in;
      eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
  Qed.

  Ltac my_update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma handleRequestVoteReply_preserves_candidate_entries :
    forall net h h' t r st' e,
      st' = handleRequestVoteReply h (snd (nwState net h)) h' t r ->
      refined_raft_intermediate_reachable net ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h
                               (update_elections_data_requestVoteReply h h' t r (nwState net h),
                                st')).
  Proof.
  unfold candidateEntries.
    intros. break_exists. break_and.
    exists x.
    split;
      rewrite update_fun_comm; simpl;
      rewrite update_fun_comm; simpl;
      my_update_destruct; subst; rewrite_update; auto;
      try (unfold update_elections_data_requestVoteReply in *;
            repeat break_match; simpl in *; auto;
           break_if; simpl in *; repeat find_rewrite; auto);
      match goal with
        | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
          remember (handleRequestVoteReply h st h' t r) as new_state
      end; find_apply_lem_hyp handleRequestVoteReply_spec; intuition;
      repeat find_rewrite; intuition.
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

  Lemma doLeader_st :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      votesReceived st' = votesReceived st /\
      currentTerm st' = currentTerm st /\
      type st' = type st.
  Proof.
    intros.
    unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; intuition.
  Qed.

  Lemma doLeader_preserves_candidateEntries :
    forall net gd d h os d' ms e,
      nwState net h = (gd, d) ->
      doLeader d h = (os, d', ms) ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h (gd, d')).
  Proof.
    intros.
    eapply candidateEntries_same; eauto;
    intros;
    repeat (rewrite update_fun_comm; simpl in * );
    my_update_destruct; subst; rewrite_update; auto;
    repeat find_rewrite; simpl; auto;
    find_apply_lem_hyp doLeader_st; intuition.
  Qed.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof.
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma pDst_deghost_packet :
    forall p : packet (params := raft_refined_multi_params),
      pDst (deghost_packet p) = pDst p.
  Proof.
    unfold deghost_packet. auto.
  Qed.
End CommonTheorems.


(* introduces a refined invariant then tries to break apart any nested
   conjunctions to return the usable invariants as hypotheses *)
Ltac intro_refined_invariant lem :=
  match goal with
  | [ h: refined_raft_intermediate_reachable _ |- _ ] =>
      let x := fresh in
      pose proof h as x;
        apply lem in x;
        unfold_invariant x
  end.
