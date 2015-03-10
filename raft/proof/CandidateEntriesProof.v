Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.
Require Import CroniesCorrectInterface.
Require Import VotesCorrectInterface.
Require Import TermSanityInterface.
Require Import CroniesTermInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CandidateEntriesInterface.

Section CandidateEntriesProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {cti : cronies_term_interface}.
  Context {tsi : term_sanity_interface}.
  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.

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

  Lemma handleClientRequest_spec :
    forall h d client id c out d' l,
      handleClientRequest h d client id c = (out, d', l) ->
      currentTerm d' = currentTerm d /\
      type d' = type d /\
      l = [] /\
      (forall e, In e (log d') ->
            (In e (log d) \/ (e = (mkEntry
                                     h
                                     client
                                     id
                                     (S (maxIndex (log d)))
                                     (currentTerm d)
                                     c) /\ log d' = e :: log d /\ type d' = Leader))).
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; intuition.
    simpl in *. intuition. subst. auto.
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

  Lemma candidate_entries_client_request :
    refined_raft_net_invariant_client_request CandidateEntries.
  Proof.
    unfold refined_raft_net_invariant_client_request, CandidateEntries.
    intros. subst.
    intuition.
    - unfold candidateEntries_host_invariant in *.
      intros; simpl in *.
      eapply candidateEntries_ext; try eassumption.
      repeat find_higher_order_rewrite.
      unfold update_elections_data_client_request in *. repeat break_let. simpl in *.
      destruct (name_eq_dec h0 h); subst.
      + rewrite_update.
        unfold update_elections_data_client_request in *. repeat break_let. simpl in *.
        simpl in *. find_inversion.
        find_apply_lem_hyp handleClientRequest_spec; intuition eauto.
        find_apply_hyp_hyp.
        intuition.
        * rewrite_update.
          eapply candidateEntries_same; eauto; intuition;
          destruct (name_eq_dec h0 h); subst; rewrite_update; auto.
          repeat break_match; simpl; auto.
        * find_apply_lem_hyp cronies_correct_invariant.
          unfold candidateEntries. exists h.
          intuition; rewrite_update; simpl in *; try congruence.
          repeat find_rewrite. simpl in *.
          repeat break_match; simpl; eauto using won_election_cronies.
      + rewrite_update.
        find_apply_lem_hyp handleClientRequest_spec.
        eapply candidateEntries_same; eauto; intuition;
        destruct (name_eq_dec h1 h); subst; rewrite_update; auto;
        tuple_inversion; repeat find_rewrite;
        repeat break_match; simpl; auto.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *.
      eapply candidateEntries_ext; try eassumption.
      find_apply_lem_hyp handleClientRequest_spec.
      intuition.
      subst. simpl in *.

      eapply_prop_hyp candidateEntries AppendEntries; eauto.
      + eapply candidateEntries_same; eauto; intuition;
        destruct (name_eq_dec h h0); subst; rewrite_update; auto.
        unfold update_elections_data_client_request; repeat break_match; simpl; auto.
      + find_apply_hyp_hyp. intuition.
  Qed.

  Lemma update_elections_data_timeout_leader_cronies_same :
    forall sigma h,
      type (snd (sigma h)) = Leader ->
      cronies (update_elections_data_timeout h (sigma h)) =
      cronies (fst (sigma h)).
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; subst; simpl in *; auto.
    unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; try congruence; repeat find_inversion; simpl in *;
    unfold raft_data in *;
    congruence.
  Qed.

  Ltac update_destruct :=
    match goal with
    | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Lemma handleTimeout_only_sends_RequestVotes :
    forall h d out d' l p,
      handleTimeout h d = (out, d', l) ->
      In p l ->
      exists t h' maxi maxt,
        snd p = RequestVote t h' maxi maxt.
  Proof.
    unfold handleTimeout, tryToBecomeLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; intuition;
    do_in_map; subst; simpl; eauto.
  Qed.

  Lemma handleTimeout_log_same :
    forall h d out d' l,
      handleTimeout h d = (out, d', l) ->
      log d' = log d.
  Proof.
    unfold handleTimeout, tryToBecomeLeader.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma handleTimeout_not_leader_inc_term :
    forall h d out d' l,
      handleTimeout h d = (out, d', l) ->
      type d <> Leader ->
      currentTerm d' = S (currentTerm d).
  Proof.
    unfold handleTimeout, tryToBecomeLeader.
    intros. simpl in *.
    repeat break_match; try congruence; repeat find_inversion; auto.
  Qed.

  Lemma update_elections_data_timeout_cronies :
    forall h d out d' l t,
      handleTimeout h (snd d) = (out, d', l) ->
      cronies (update_elections_data_timeout h d) t = cronies (fst d) t \/
      (t = currentTerm d' /\
       cronies (update_elections_data_timeout h d) t = votesReceived d').
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; repeat find_inversion; simpl; auto.
    break_match; auto.
  Qed.

  Lemma handleTimeout_preserves_candidateEntries :
    forall net h e out d l,
      refined_raft_intermediate_reachable net ->
      handleTimeout h (snd (nwState net h)) = (out, d, l) ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h (update_elections_data_timeout h (nwState net h), d)).
  Proof.
    intros.
    destruct (serverType_eq_dec (type (snd (A:=electionsData) (B:=raft_data) (nwState net h))) Leader).
      + (* Leader case *)
        unfold handleTimeout, tryToBecomeLeader in *. simpl in *.
        find_rewrite. find_inversion.

        eapply candidateEntries_same; eauto;
        intros;
        repeat (rewrite update_fun_comm; simpl in * );
        update_destruct; subst; rewrite_update;
        auto using update_elections_data_timeout_leader_cronies_same.
      + (* non-Leader case *)

        unfold candidateEntries in *.
        break_exists. break_and.
        exists x.
        rewrite update_fun_comm; simpl.
        rewrite update_fun_comm; simpl.
        rewrite update_fun_comm; simpl.
        rewrite update_fun_comm; simpl.
        rewrite update_fun_comm with (f := type); simpl.
        update_destruct; subst; rewrite_update; auto.
        split.
        * match goal with
          | [ H : handleTimeout _ _ = _ |- _ ] =>
            pose proof H;
              apply update_elections_data_timeout_cronies with (t := eTerm e) in H
          end.
          intuition; find_rewrite; auto.
          find_apply_lem_hyp wonElection_exists_voter.
          break_exists.
          find_apply_lem_hyp in_dedup_was_in.
          find_copy_apply_lem_hyp cronies_term_invariant; auto.
          find_copy_apply_lem_hyp handleTimeout_not_leader_inc_term; auto.
          simpl in *.
          omega.
        * intros.
          find_apply_lem_hyp wonElection_exists_voter.
          break_exists.
          find_apply_lem_hyp in_dedup_was_in.
          find_copy_apply_lem_hyp cronies_term_invariant; auto.
          find_copy_apply_lem_hyp handleTimeout_not_leader_inc_term; auto.
          simpl in *.
          omega.
  Qed.

  Lemma candidate_entries_timeout :
    refined_raft_net_invariant_timeout CandidateEntries.
  Proof.
    unfold refined_raft_net_invariant_timeout, CandidateEntries.
    intros. subst.
    intuition; simpl in *.
    - unfold candidateEntries_host_invariant in *.
      intros.
      eapply candidateEntries_ext; try eassumption.
      repeat find_higher_order_rewrite.

        find_rewrite_lem update_fun_comm. simpl in *.
        find_rewrite_lem update_fun_comm. simpl in *.
        erewrite handleTimeout_log_same in * by eauto.

        find_rewrite_lem_by update_nop_ext' auto.
        find_apply_hyp_hyp.
        eauto using handleTimeout_preserves_candidateEntries.
    - unfold candidateEntries_nw_invariant in *.
      intros.
      simpl in *.
      eapply candidateEntries_ext; eauto.
      find_apply_hyp_hyp.
      break_or_hyp.
      + eapply_prop_hyp pBody pBody; eauto.
        eauto using handleTimeout_preserves_candidateEntries.
      + do_in_map. subst. simpl in *.
        eapply handleTimeout_only_sends_RequestVotes in H8; eauto.
        break_exists. congruence.
  Qed.

  Lemma update_elections_data_appendEntries_cronies_same :
    forall h d t n pli plt es ci,
      cronies (update_elections_data_appendEntries h d t n pli plt es ci) =
      cronies (fst d).
  Proof.
    unfold update_elections_data_appendEntries.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma handleAppendEntries_spec :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      (currentTerm st <= currentTerm st' /\
       (forall e,
          In e (log st') ->
          In e (log st) \/
          In e es /\ currentTerm st' = t) /\
       ~ is_append_entries m).
  Proof.
    intros.
    unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try solve [break_exists; congruence];
    in_crush; eauto using removeAfterIndex_in.
  Qed.


  Lemma handleAppendEntries_term_same_or_type_follower :
    forall h t n pli plt es ci d m st,
      handleAppendEntries h st t n pli plt es ci = (d, m) ->
      (currentTerm d = currentTerm st /\ type d = type st) \/ type d = Follower.
  Proof.
    unfold handleAppendEntries in *.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; try congruence.
  Qed.

  Lemma handleAppendEntries_preserves_candidate_entries :
    forall net h t n pli plt es ci d m e,
      handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) ->
      refined_raft_intermediate_reachable net ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h
                                 (update_elections_data_appendEntries
                                    h
                                    (nwState net h) t n pli plt es ci, d)).
  Proof.
    unfold candidateEntries.
    intros. break_exists. break_and.
    exists x.
    split.
    - rewrite update_fun_comm. simpl.
      rewrite update_fun_comm. simpl.
      rewrite update_elections_data_appendEntries_cronies_same.
      destruct (name_eq_dec x h); subst; rewrite_update; auto.
    - intros.
      rewrite update_fun_comm. simpl.
      find_rewrite_lem update_fun_comm. simpl in *.
      destruct (name_eq_dec x h); subst; rewrite_update; auto.
      find_apply_lem_hyp handleAppendEntries_term_same_or_type_follower.
      intro; intuition;
      repeat find_rewrite; auto; discriminate.
  Qed.

  Ltac my_update_destruct :=
    match goal with
    | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma is_append_entries_intro :
    forall t n plt pli es ci,
      is_append_entries (AppendEntries t n pli plt es ci).
  Proof.
    eauto 20.
  Qed.

  Lemma candidate_entries_append_entries :
    refined_raft_net_invariant_append_entries CandidateEntries.
  Proof.
    red. unfold CandidateEntries.
    intros. subst.
    intuition; simpl in *.
    - unfold candidateEntries_host_invariant in *.
      intros.
      eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      my_update_destruct; subst; rewrite_update;
      eapply handleAppendEntries_preserves_candidate_entries; eauto.
      find_copy_apply_lem_hyp handleAppendEntries_spec. break_and.
      find_apply_hyp_hyp. intuition eauto.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *.
      eapply candidateEntries_ext; eauto.
      find_apply_hyp_hyp.
      intuition.
      + eapply handleAppendEntries_preserves_candidate_entries; eauto.
      + subst. simpl in *. find_apply_lem_hyp handleAppendEntries_spec.
        break_and.
        subst.
        exfalso.
        eauto using is_append_entries_intro.
  Qed.

  Lemma handleAppendEntriesReply_spec :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      log st' = log st /\
      ((currentTerm st' = currentTerm st /\ type st' = type st)
       \/ type st' = Follower) /\
      (forall m, In m ms -> ~ is_append_entries (snd m)).
  Proof.
    intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition.
  Qed.


  Lemma handleAppendEntriesReply_preserves_candidate_entries :
    forall net h h' t es r st' ms e,
      handleAppendEntriesReply h (snd (nwState net h)) h' t es r = (st', ms) ->
      refined_raft_intermediate_reachable net ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h (fst (nwState net h), st')).
  Proof.
    unfold candidateEntries.
    intros. break_exists. break_and.
    exists x.
    split.
    - rewrite update_fun_comm. simpl.
      rewrite update_fun_comm. simpl.
      my_update_destruct; subst; rewrite_update; auto.
    - intros. my_update_destruct; subst; rewrite_update; auto.
      simpl in *.
      find_apply_lem_hyp handleAppendEntriesReply_spec.
      intuition; repeat find_rewrite; intuition.
      congruence.
  Qed.


  Ltac prove_in :=
    match goal with
      | [ _ : nwPackets ?net = _,
              _ : In (?p : packet) _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition)
      | [ _ : nwPackets ?net = _,
              _ : pBody ?p = _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; intuition)
    end.

  Lemma candidate_entries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply CandidateEntries.
  Proof.
    red. unfold CandidateEntries. intros. intuition.
    - unfold candidateEntries_host_invariant in *.
      intros. simpl in *. eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      my_update_destruct.
      + subst. rewrite_update.
        unfold candidateEntries in *.
        find_apply_lem_hyp handleAppendEntriesReply_spec. break_and.
        repeat find_rewrite.
        find_apply_hyp_hyp.
        break_exists; exists x; eauto.
        my_update_destruct; intuition; subst; rewrite_update; simpl in *; auto;
        repeat find_rewrite; intuition; congruence.
      + rewrite_update. find_apply_hyp_hyp.
        eauto using handleAppendEntriesReply_preserves_candidate_entries.
    - unfold candidateEntries_nw_invariant in *. intros. simpl in *.
      find_apply_hyp_hyp. intuition.
      + (* packet already in nw *)
        prove_in.
        eapply candidateEntries_ext; eauto.
        find_eapply_lem_hyp handleAppendEntriesReply_preserves_candidate_entries; eauto.
        subst. auto.
      + exfalso.
        do_in_map.
        find_eapply_lem_hyp handleAppendEntriesReply_spec; eauto.
        subst. simpl in *. find_rewrite.
        match goal with
          | H : ~ is_append_entries _ |- _ => apply H
        end.
        repeat eexists; eauto.
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

  Lemma handleRV_advanceCurrentTerm_preserves_candidateEntries :
    forall net h h' t lli llt e,
      candidateEntries e (nwState net) ->
      candidateEntries e
                       (update (nwState net) h
                               (update_elections_data_requestVote h h' t h' lli llt (nwState net h),
                                advanceCurrentTerm (snd (nwState net h)) t)).
  Proof.
    intros.
    unfold candidateEntries in *.
    break_exists.  break_and.
    exists x.
    split; update_destruct; subst; rewrite_update; auto; simpl.
    + rewrite update_elections_data_requestVote_cronies_same. auto.
    + intros.
      match goal with
      | [ |- context [advanceCurrentTerm ?st ?t] ] =>
        pose proof advanceCurrentTerm_same_or_type_follower st t
      end.
      intuition; try congruence.
      repeat find_rewrite. auto.
  Qed.

  Lemma handleRequestVote_preserves_candidateEntries :
    forall net h h' t lli llt d e m,
      handleRequestVote h (snd (nwState net h)) t h' lli llt = (d, m) ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h
                                 (update_elections_data_requestVote
                                    h h' t h' lli llt (nwState net h), d)).
  Proof.
    unfold handleRequestVote.
    intros.
    repeat break_match; repeat find_inversion;
    auto using handleRV_advanceCurrentTerm_preserves_candidateEntries.
    - eapply candidateEntries_same; eauto;
        intros;
        repeat (rewrite update_fun_comm; simpl in * );
        update_destruct; subst; rewrite_update;
        auto using update_elections_data_requestVote_cronies_same.
    - do_bool. intuition. congruence.
    - unfold candidateEntries in *. break_exists. break_and. exists x.
      simpl.
      split.
      + rewrite update_fun_comm with (f := fst). simpl.
        rewrite update_fun_comm with (f := cronies). simpl.
        rewrite update_elections_data_requestVote_cronies_same.
        update_destruct; subst; rewrite_update; auto.
      + rewrite update_fun_comm with (f := snd). simpl.
        rewrite update_fun_comm with (f := currentTerm). simpl.
        rewrite update_fun_comm with (f := type). simpl.
        update_destruct; subst; rewrite_update; auto.
        match goal with
        | [ |- context [advanceCurrentTerm ?st ?t] ] =>
          pose proof advanceCurrentTerm_same_or_type_follower st t
        end.
        intuition; try congruence.
        repeat find_rewrite. auto.
  Qed.

  Lemma handleRequestVote_only_sends_RVR :
    forall d h h' t lli llt d' m,
      handleRequestVote h d t h' lli llt = (d', m) ->
      is_request_vote_reply m.
  Proof.
    unfold handleRequestVote.
    intros.
    repeat break_match; repeat find_inversion; eauto.
  Qed.

  Lemma candidate_entries_request_vote :
    refined_raft_net_invariant_request_vote CandidateEntries.
  Proof.
    red. unfold CandidateEntries.
    intros. subst.
    intuition; simpl in *.
    - unfold candidateEntries_host_invariant in *.
      intros.
      eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      my_update_destruct; subst; rewrite_update; simpl in *;
      try find_erewrite_lem handleRequestVote_same_log;
      eapply handleRequestVote_preserves_candidateEntries; eauto.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *.
      eapply candidateEntries_ext; eauto.
      find_apply_hyp_hyp. intuition.
      + eauto using handleRequestVote_preserves_candidateEntries.
      + subst. simpl in *.
        find_apply_lem_hyp handleRequestVote_only_sends_RVR.
        subst. break_exists. discriminate.
  Qed.

  Lemma handleRequestVoteReply_spec :
    forall h st h' t r st',
      st' = handleRequestVoteReply h st h' t r ->
      log st' = log st /\
      (forall v, In v (votesReceived st) -> In v (votesReceived st')) /\
      ((currentTerm st' = currentTerm st /\ type st' = type st)
       \/ type st' <> Candidate) /\
      (type st <> Leader /\ type st' = Leader ->
       (type st = Candidate /\ wonElection (dedup name_eq_dec
                                                  (votesReceived st')) = true)).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try right; congruence.
  Qed.

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
    split.
    - rewrite update_fun_comm. simpl.
      rewrite update_fun_comm. simpl.
      my_update_destruct; subst; rewrite_update; auto.
      unfold update_elections_data_requestVoteReply in *.
      repeat break_match; simpl in *; auto.
      + break_if; simpl in *; repeat find_rewrite; auto.
         match goal with
          | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
            remember (handleRequestVoteReply h st h' t r) as new_state
         end. find_apply_lem_hyp handleRequestVoteReply_spec. intuition.
         repeat find_rewrite. intuition.
      + break_if; simpl in *; find_rewrite; auto.
        match goal with
          | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
            remember (handleRequestVoteReply h st h' t r) as new_state
        end. find_apply_lem_hyp handleRequestVoteReply_spec. intuition.
        repeat find_rewrite. intuition.
      +  break_if; simpl in *; find_rewrite; auto.
        match goal with
          | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
            remember (handleRequestVoteReply h st h' t r) as new_state
        end. find_apply_lem_hyp handleRequestVoteReply_spec. intuition.
        repeat find_rewrite. intuition.
        * find_apply_lem_hyp cronies_correct_invariant.
          unfold cronies_correct in *. intuition.
          unfold votes_received_leaders in *.
          match goal with
            | H :  Leader = _ |- _ =>
              symmetry in H
          end. find_apply_hyp_hyp.
          eapply wonElection_no_dup_in;
            eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
        * destruct (serverType_eq_dec (type (snd (nwState net x))) Leader); intuition.
          find_apply_lem_hyp cronies_correct_invariant; auto.
          eapply wonElection_no_dup_in;
            eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
    - rewrite update_fun_comm. simpl.
      rewrite update_fun_comm. simpl.
      my_update_destruct; subst; rewrite_update; auto.
      match goal with
          | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
            remember (handleRequestVoteReply h st h' t r) as new_state
      end. find_apply_lem_hyp handleRequestVoteReply_spec. intuition.
      repeat find_rewrite. intuition.
  Qed.

  Lemma candidate_entries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply CandidateEntries.
    red. unfold CandidateEntries. intros. intuition.
    - unfold candidateEntries_host_invariant in *.
      intros. simpl in *. eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      my_update_destruct.
      + subst. rewrite_update.
        match goal with
          | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
            remember (handleRequestVoteReply h st h' t r) as new_state
        end.
        find_copy_apply_lem_hyp handleRequestVoteReply_spec. break_and.
        match goal with
          | H : log _ = log _ |- _ => rewrite H in *
        end.
        find_apply_hyp_hyp.
        eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
      + rewrite_update.
        eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *. eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
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
    update_destruct; subst; rewrite_update; auto;
    repeat find_rewrite; simpl; auto;
    find_apply_lem_hyp doLeader_st; intuition.
  Qed.

  Lemma doLeader_in_entries :
    forall (h : name) d h os d' ms m t li pli plt es ci e,
      doLeader d h = (os, d', ms) ->
      snd m = AppendEntries t li pli plt es ci ->
      In m ms ->
      In e es ->
      In e (log d).
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; intuition.
    do_in_map.

    unfold replicaMessage in *. simpl in *. subst. simpl in *.
    find_inversion.
    eauto using findGtIndex_in.
  Qed.

  Lemma candidate_entries_do_leader :
    refined_raft_net_invariant_do_leader CandidateEntries.
  Proof.
    red. unfold CandidateEntries.
    intros.
    intuition; simpl in *.
    - unfold candidateEntries_host_invariant in *.
      intros.
      eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      my_update_destruct; subst; rewrite_update.
      + simpl in *.
        find_erewrite_lem doLeader_same_log.
        repeat match goal with
        | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] =>
          replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto)
        end.
        eauto using doLeader_preserves_candidateEntries.
      + eauto using doLeader_preserves_candidateEntries.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *.
      eapply candidateEntries_ext; eauto.
      find_apply_hyp_hyp.
      intuition.
      + eauto using doLeader_preserves_candidateEntries.
      + do_in_map. subst. simpl in *.
        eapply doLeader_preserves_candidateEntries; eauto.
        eapply_prop candidateEntries_host_invariant.
        match goal with
        | [ H : _ |- _ ] => rewrite H
        end.
        simpl.
        eauto using doLeader_in_entries.
  Qed.

  Lemma doGenericServer_same_type :
    forall h d os d' ms,
      doGenericServer h d = (os, d', ms) ->
      type d' = type d.
  Proof.
    unfold doGenericServer.
    intros.
    repeat break_match; repeat find_inversion;
    use_applyEntries_spec; subst; simpl in *;
    auto.
  Qed.

  Lemma doGenericServer_spec :
    forall h d os d' ms,
      doGenericServer h d = (os, d', ms) ->
      (log d' = log d /\ currentTerm d' = currentTerm d /\
       (forall m, In m ms -> ~ is_append_entries (snd m))).
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion; subst; intuition;
    use_applyEntries_spec; subst; simpl in *; auto.
  Qed.

  Lemma doGenericServer_preserves_candidateEntries :
    forall net gd d h os d' ms e,
      nwState net h = (gd, d) ->
      doGenericServer h d = (os, d', ms) ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h (gd, d')).
  Proof.
    intros.
    eapply candidateEntries_same; eauto;
    intros;
    repeat (rewrite update_fun_comm; simpl in * );
    update_destruct; subst; rewrite_update; auto;
    repeat find_rewrite; simpl; auto.
    - find_copy_apply_lem_hyp doGenericServer_spec. break_and. auto.
    - eauto using doGenericServer_same_type.
  Qed.

  Lemma candidate_entries_do_generic_server :
    refined_raft_net_invariant_do_generic_server CandidateEntries.
  Proof.
    red. unfold CandidateEntries.
    intros.
    intuition; simpl in *.
    - unfold candidateEntries_host_invariant in *.
      intros.
      eapply candidateEntries_ext; eauto.
      repeat find_higher_order_rewrite.
      my_update_destruct; subst; rewrite_update.
      + simpl in *.
        find_copy_apply_lem_hyp doGenericServer_spec. break_and.
        find_rewrite.
        repeat match goal with
        | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] =>
          replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto)
        end.
        eauto using doGenericServer_preserves_candidateEntries.
      + eauto using doGenericServer_preserves_candidateEntries.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *.
      eapply candidateEntries_ext; eauto.
      find_apply_hyp_hyp.
      intuition.
      + eauto using doGenericServer_preserves_candidateEntries.
      + do_in_map.
        find_copy_apply_lem_hyp doGenericServer_spec. break_and.
        subst. simpl in *.
        find_apply_hyp_hyp.
        exfalso.
        find_rewrite. eauto 20.
  Qed.

  Lemma candidate_entries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset CandidateEntries.
  Proof.
    red. unfold CandidateEntries.
    intros.
    intuition.
    - unfold candidateEntries_host_invariant in *.
      intros.
      repeat find_reverse_higher_order_rewrite.
      apply candidateEntries_ext with (sigma := nwState net); eauto.
    - unfold candidateEntries_nw_invariant in *.
      intros.
      find_apply_hyp_hyp.
      eapply_prop_hyp In In; eauto.
      apply candidateEntries_ext with (sigma := nwState net); eauto.
  Qed.

  Lemma reboot_log_same :
    forall d,
      log (reboot d) = log d.
  Proof.
    unfold reboot.
    auto.
  Qed.

  Lemma reboot_preservers_candidateEntries :
    forall net h d gd e,
      nwState net h = (gd, d) ->
      candidateEntries e (nwState net) ->
      candidateEntries e (update (nwState net) h (gd, reboot d)).
  Proof.
    unfold reboot, candidateEntries.
    intros.
    break_exists.
    exists x.
    break_and.
    rewrite update_fun_comm. simpl in *.
    my_update_destruct; subst; rewrite_update; auto.
    repeat find_rewrite. simpl in *. intuition. discriminate.
  Qed.

  Lemma candidate_entries_reboot :
    refined_raft_net_invariant_reboot CandidateEntries.
  Proof.
    red. unfold CandidateEntries.
    intros.
    intuition.
    - unfold candidateEntries_host_invariant in *.
      intros.
      repeat find_higher_order_rewrite.
      eapply candidateEntries_ext; eauto.
      subst.
      find_rewrite_lem update_fun_comm. simpl in *.
      find_rewrite_lem update_fun_comm. simpl in *.
      my_update_destruct; subst; rewrite_update.
      + repeat match goal with
        | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] =>
          replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto)
        end.
        find_apply_hyp_hyp.
        eauto using reboot_preservers_candidateEntries.
      + eauto using reboot_preservers_candidateEntries.
    - unfold candidateEntries_nw_invariant in *.
      intros.
      repeat find_reverse_rewrite.
      eapply_prop_hyp In In; eauto.
      eapply candidateEntries_ext; eauto.
      eauto using reboot_preservers_candidateEntries.
  Qed.

  Lemma candidate_entries_init :
    refined_raft_net_invariant_init CandidateEntries.
  Proof.
    red.
    unfold CandidateEntries.
    unfold candidateEntries_host_invariant, candidateEntries_nw_invariant.
    intuition;
     repeat match goal with
            | [ H : In _ _ |- _ ] => compute in H
            end;
    intuition.
  Qed.

  Theorem candidate_entries_invariant :
    forall (net : network),
      refined_raft_intermediate_reachable net ->
      CandidateEntries net.
  Proof.
    intros.
    eapply refined_raft_net_invariant; eauto.
    - apply candidate_entries_init.
    - apply candidate_entries_client_request.
    - apply candidate_entries_timeout.
    - apply candidate_entries_append_entries.
    - apply candidate_entries_append_entries_reply.
    - apply candidate_entries_request_vote.
    - apply candidate_entries_request_vote_reply.
    - apply candidate_entries_do_leader.
    - apply candidate_entries_do_generic_server.
    - apply candidate_entries_state_same_packet_subset.
    - apply candidate_entries_reboot.
  Qed.

  Instance cei : candidate_entries_interface.
  Proof.
    split.
    auto using candidate_entries_invariant.
  Qed.
End CandidateEntriesProof.
