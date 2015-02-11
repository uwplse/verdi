Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinement.

Require Import CommonTheorems.
Require Import CroniesCorrect.

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
        * unfold candidateEntries in *.
          find_apply_hyp_hyp. break_exists.
          exists x.
          destruct (name_eq_dec x h);
            subst; rewrite_update; intuition eauto.
          simpl in *.
          repeat find_rewrite; intuition.
        * find_apply_lem_hyp cronies_correct_invariant.
          unfold candidateEntries. exists h.
          intuition; rewrite_update; simpl in *; try congruence.
          repeat find_rewrite. simpl in *.
          eauto using won_election_cronies.
      + rewrite_update.
        unfold candidateEntries in *.
        find_apply_hyp_hyp. break_exists.
        exists x. destruct (name_eq_dec x h); subst;
             intuition; rewrite_update; simpl in *; auto.
        find_apply_lem_hyp handleClientRequest_spec.
        intuition. repeat find_rewrite. auto.
  Admitted.

  Lemma candidate_entries_timeout :
    refined_raft_net_invariant_timeout CandidateEntries.
  Admitted.

  Lemma candidate_entries_append_entries :
    refined_raft_net_invariant_append_entries CandidateEntries.
  Admitted.

  Lemma candidate_entries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply CandidateEntries.
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
