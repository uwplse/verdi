Require Import GhostSimulations.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import RefinementCommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AllEntriesLeaderSublogInterface.

Require Import CandidateEntriesInterface.
Require Import AllEntriesCandidateEntriesInterface.
Require Import VotesCorrectInterface.
Require Import CroniesCorrectInterface.
Require Import LeaderSublogInterface.
Require Import OneLeaderPerTermInterface.

Section AllEntriesLeaderSublog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {cei : candidate_entries_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {olpti : one_leader_per_term_interface}.

  Context {aecei : allEntries_candidate_entries_interface}.
  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.

  Lemma lifted_leader_sublog_nw :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (snd (nwState net h)) = Leader ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ leader_sublog_invariant_invariant _ ltac:(eauto)) as Hinv.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant in *.
    destruct Hinv as [Hhost Hnw].
    find_apply_lem_hyp ghost_packet.
    eapply_prop_hyp In In; eauto; try find_rewrite_lem deghost_spec; try rewrite deghost_spec; eauto.
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

  Lemma map_snd :
    forall {A B} (a : A) (b : B) l,
      In (a, b) l ->
      In b (map snd l).
  Proof.
    intros.
    apply in_map_iff.
    eexists; intuition; eauto; reflexivity.
  Qed.

  Hint Resolve map_snd.
  
  Lemma allEntries_leader_sublog_client_request :
    refined_raft_net_invariant_client_request allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleClientRequest_type. intuition.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *.
    - find_apply_lem_hyp update_elections_data_client_request_log_allEntries.
      intuition; repeat find_rewrite; eauto.
      break_exists. intuition. repeat find_rewrite. simpl in *.
      intuition; repeat find_rewrite; eauto; solve_by_inversion.
    - find_apply_lem_hyp update_elections_data_client_request_log_allEntries.
      intuition; repeat find_rewrite; eauto.
      break_exists. intuition. repeat find_rewrite. simpl in *.
      intuition; repeat find_rewrite; eauto; solve_by_inversion.
    - find_apply_lem_hyp update_elections_data_client_request_log_allEntries.
      intuition; repeat find_rewrite; eauto.
      break_exists. intuition. repeat find_rewrite. simpl in *.
      intuition; repeat find_rewrite; eauto.
      tuple_inversion.
      repeat find_rewrite.
      find_false.
      eapply lifted_one_leader_per_term; eauto.
  Qed.

  Lemma update_elections_data_appendEntries_log_allEntries_leader
     : forall (h : name) (st : electionsData * raft_data) 
         (t : term) (n : name) (pli : logIndex) (plt : term)
         (es : list entry) (ci : logIndex) (st' : raft_data) 
         (ps : msg),
         handleAppendEntries h (snd st) t n pli plt es ci = (st', ps) ->
         type st' = Leader ->
         (currentTerm st' = currentTerm (snd st) /\
          type (snd st) = Leader /\
           log st' = log (snd st) /\
          allEntries
            (update_elections_data_appendEntries h st t n pli plt es ci) =
          allEntries (fst st)).
  Proof.
    intros.
    unfold update_elections_data_appendEntries in *.
    unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; repeat find_inversion; subst; simpl in *; auto;
    congruence.
  Qed.

  Lemma allEntries_leader_sublog_append_entries :
    refined_raft_net_invariant_append_entries allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *.
    - find_eapply_lem_hyp update_elections_data_appendEntries_log_allEntries_leader; eauto.
      intuition.
      repeat find_rewrite; eauto.
    - find_eapply_lem_hyp update_elections_data_appendEntries_log_allEntries_leader; eauto.
      intuition.
      repeat find_rewrite; eauto.
    - find_eapply_lem_hyp update_elections_data_appendEntries_allEntries_term'; eauto.
      intuition;
        eauto using lifted_leader_sublog_nw.
  Qed.

  Lemma allEntries_leader_sublog_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *;
    find_copy_apply_lem_hyp handleAppendEntriesReply_type;
    find_apply_lem_hyp handleAppendEntriesReply_log;
    intuition; repeat find_rewrite; eauto; congruence.
  Qed.
  
  Lemma allEntries_leader_sublog_request_vote :
    refined_raft_net_invariant_request_vote allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *;
    find_copy_apply_lem_hyp handleRequestVote_type;
    find_apply_lem_hyp handleRequestVote_log;
    try find_erewrite_lem update_elections_data_requestVote_allEntries; eauto;
    intuition; repeat find_rewrite; eauto; try congruence.
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

  Lemma allEntries_leader_sublog_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    match goal with
      | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?v] =>
        pose proof handleRequestVoteReply_spec h st h' t v
             (handleRequestVoteReply h st h' t v)
    end.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *;
    try find_rewrite_lem update_elections_data_requestVoteReply_allEntries;
    intuition; repeat find_rewrite; eauto; try congruence.
    - match goal with
        | _ : context [type ?st = Leader -> False] |- _ =>
          destruct (serverType_eq_dec (type st) Leader)
      end; eauto.
      + match goal with
          | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ =>
            pose proof handleRequestVoteReply_type h st h' t v
                 (handleRequestVoteReply h st h' t v)
        end.
        intuition; repeat find_rewrite; try congruence.
        eauto.
      + intuition.
        find_copy_apply_lem_hyp allEntries_candidateEntries_invariant; auto.
        match goal with
          | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ =>
            pose proof handleRequestVoteReply_RVR_spec h st h' t v
                 (handleRequestVoteReply h st h' t v)
        end. intuition; repeat find_rewrite; try congruence.
        subst.
        find_eapply_lem_hyp wonElection_candidateEntries_rvr;
          eauto using votes_correct_invariant, cronies_correct_invariant.
        unfold ghost_data in *. simpl in *.
        unfold raft_refined_base_params, raft_refined_multi_params in *.
        congruence.
    - match goal with
        | _ : context [type ?st = Leader -> False] |- _ =>
          destruct (serverType_eq_dec (type st) Leader)
      end; eauto.
      + match goal with
          | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ =>
            pose proof handleRequestVoteReply_type h st h' t v
                 (handleRequestVoteReply h st h' t v)
        end.
        intuition; repeat find_rewrite; try congruence.
        eauto.
      + intuition.
        find_copy_apply_lem_hyp allEntries_candidateEntries_invariant; auto.
        match goal with
          | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ =>
            pose proof handleRequestVoteReply_RVR_spec h st h' t v
                 (handleRequestVoteReply h st h' t v)
        end. intuition; repeat find_rewrite; try congruence.
        subst.
        find_eapply_lem_hyp wonElection_candidateEntries_rvr;
          eauto using votes_correct_invariant, cronies_correct_invariant.
        unfold ghost_data in *. simpl in *.
        unfold raft_refined_base_params, raft_refined_multi_params in *.
        congruence.
  Qed.

  Lemma allEntries_leader_sublog_timeout :
    refined_raft_net_invariant_timeout allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *;
    find_copy_apply_lem_hyp handleTimeout_type;
    find_apply_lem_hyp handleTimeout_log_same;
    try find_rewrite_lem update_elections_data_timeout_allEntries;
    intuition; repeat find_rewrite; eauto; try congruence.
  Qed.


  Lemma allEntries_leader_sublog_do_leader :
    refined_raft_net_invariant_do_leader allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *;
    find_copy_apply_lem_hyp doLeader_type;
    find_apply_lem_hyp doLeader_log;
    intuition; repeat find_rewrite; eauto; try congruence.
  Qed.
  

  Lemma allEntries_leader_sublog_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    do_in_map; subst;
    destruct x; simpl in *;
    find_copy_apply_lem_hyp doGenericServer_type;
    find_apply_lem_hyp doGenericServer_log;
    try find_rewrite_lem update_elections_data_timeout_allEntries;
    intuition; repeat find_rewrite; eauto; try congruence.
  Qed.


  Lemma allEntries_leader_sublog_reboot :
    refined_raft_net_invariant_reboot allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_higher_order_rewrite.
    simpl in *.
    destruct_update; simpl in *; eauto; congruence.
  Qed.

  Lemma allEntries_leader_sublog_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma allEntries_leader_sublog_init :
    refined_raft_net_invariant_init allEntries_leader_sublog.
  Proof.
    red. unfold allEntries_leader_sublog. intros. simpl in *.
    congruence.
  Qed.
  
  Instance aelsi : allEntries_leader_sublog_interface.
  split. intros.
  apply refined_raft_net_invariant; auto.
  - apply allEntries_leader_sublog_init.
  - apply allEntries_leader_sublog_client_request.
  - apply allEntries_leader_sublog_timeout.
  - apply allEntries_leader_sublog_append_entries.
  - apply allEntries_leader_sublog_append_entries_reply.
  - apply allEntries_leader_sublog_request_vote.
  - apply allEntries_leader_sublog_request_vote_reply.
  - apply allEntries_leader_sublog_do_leader.
  - apply allEntries_leader_sublog_do_generic_server.
  - apply allEntries_leader_sublog_state_same_packet_subset.
  - apply allEntries_leader_sublog_reboot.
  Qed.
  
End AllEntriesLeaderSublog.
