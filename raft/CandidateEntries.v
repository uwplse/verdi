Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinement.

Require Import CommonTheorems.
Require Import CroniesCorrect.
Require Import VotesCorrect.
Require Import TermSanity.
Require Import CroniesTerm.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section CandidateEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition candidateEntries e (sigma : name -> _) :=
    exists h,
      wonElection (dedup name_eq_dec (cronies (fst (sigma h)) (eTerm e))) = true /\
      (currentTerm (snd (sigma h)) = eTerm e ->
       type (snd (sigma h)) <> Candidate).

  Lemma candidateEntries_ext :
    forall e sigma sigma',
      (forall h, sigma' h = sigma h) ->
      candidateEntries e sigma ->
      candidateEntries e sigma'.
  Proof.
    unfold candidateEntries.
    firstorder.
    exists x; intuition;
    repeat find_higher_order_rewrite; auto.
  Qed.

  Definition candidateEntries_host_invariant sigma :=
    (forall h e, In e (log (snd (sigma h))) ->
                 candidateEntries e sigma).

  Definition candidateEntries_nw_invariant net :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      forall e,
        In e entries ->
        candidateEntries e (nwState net).

  Definition CandidateEntries net : Prop :=
    candidateEntries_host_invariant (nwState net) /\ candidateEntries_nw_invariant net.

  Lemma handleClientRequest_spec :
    forall h d id c out d' l,
      handleClientRequest h d id c = (out, d', l) ->
      currentTerm d' = currentTerm d /\
      type d' = type d /\
      l = [] /\
      (forall e, In e (log d') ->
            (In e (log d) \/ (e = (mkEntry
                                     h
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
    firstorder. eexists.
    repeat find_higher_order_rewrite.
    eauto.
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

      destruct (name_eq_dec h0 h); subst.
      + rewrite_update.
        simpl in *.
        find_apply_lem_hyp handleClientRequest_spec; intuition eauto.
        find_apply_hyp_hyp.
        intuition.
        * rewrite_update.
          eapply candidateEntries_same; eauto; intuition;
          destruct (name_eq_dec h0 h); subst; rewrite_update; auto.
        * find_apply_lem_hyp cronies_correct_invariant.
          unfold candidateEntries. exists h.
          intuition; rewrite_update; simpl in *; try congruence.
          repeat find_rewrite. simpl in *.
          eauto using won_election_cronies.
      + rewrite_update.
        find_apply_lem_hyp handleClientRequest_spec.
        eapply candidateEntries_same; eauto; intuition;
        destruct (name_eq_dec h1 h); subst; rewrite_update; auto.
    - unfold candidateEntries_nw_invariant in *.
      intros. simpl in *.
      eapply candidateEntries_ext; try eassumption.
      find_apply_lem_hyp handleClientRequest_spec.
      intuition.
      subst. simpl in *.

      eapply_prop_hyp candidateEntries AppendEntries; eauto.
      + eapply candidateEntries_same; eauto; intuition;
        destruct (name_eq_dec h h0); subst; rewrite_update; auto.
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

  Ltac find_rewrite_lem lem :=
    match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H; [idtac]
    end.

  Ltac find_rewrite_lem_by lem t :=
    match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H by t
    end.

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
        
    
  Admitted.

  Lemma candidate_entries_request_vote :
    refined_raft_net_invariant_request_vote CandidateEntries.
  Admitted.

  Lemma candidate_entries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply CandidateEntries.
  Admitted.

  Lemma candidate_entries_do_leader :
    refined_raft_net_invariant_do_leader CandidateEntries.
  Admitted.

  Lemma candidate_entries_do_generic_server :
    refined_raft_net_invariant_do_generic_server CandidateEntries.
  Admitted.

  Lemma candidate_entries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset CandidateEntries.
  Admitted.

  Lemma candidate_entries_reboot :
    refined_raft_net_invariant_reboot CandidateEntries.
  Admitted.

  Lemma candidate_entries_init :
    refined_raft_net_invariant_init CandidateEntries.
  Admitted.

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
End CandidateEntries.
