Require Import List.
Require Import Omega.

Require Import Util.
Require Import VerdiTactics.
Require Import Net.
Require Import GhostSimulations.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import LeaderLogsContiguousInterface.
Require Import LogMatchingInterface.

Require Import SpecLemmas.

Section LeaderLogsContiguous.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lmi : log_matching_interface}.

  Ltac update_destruct_hyp :=
    match goal with
    | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.
  

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

  Lemma handleRequestVoteReply_spec :
    forall h st h' t v st',
      st' = handleRequestVoteReply h st h' t v ->
      log st' = log st /\
      (currentTerm st' = currentTerm st \/
       (currentTerm st <= currentTerm st' /\
        type st' = Follower)).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition.
  Qed.
  
  Lemma update_elections_data_requestVoteReply_leaderLogs :
    forall h h' t r st,
      leaderLogs (update_elections_data_requestVoteReply h h' t r st) =
      leaderLogs (fst st) \/
      leaderLogs (update_elections_data_requestVoteReply h h' t r st) =
      (currentTerm (snd st), log (snd st)) :: leaderLogs (fst st).
  Proof.
    intros.
    unfold update_elections_data_requestVoteReply in *.
    repeat break_match; intuition.
    simpl in *.
    match goal with
      | |- context [handleRequestVoteReply ?h ?s ?h' ?t ?r] =>
        pose proof handleRequestVoteReply_spec
             h s h' t r (handleRequestVoteReply h s h' t r)
    end. intuition; repeat find_rewrite; intuition.
    congruence.
  Qed.      

  Theorem lift_log_matching :
    forall net,
      refined_raft_intermediate_reachable net ->
      log_matching (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using log_matching_invariant.
  Qed.

  Theorem logs_contiguous :
    forall net h,
      refined_raft_intermediate_reachable net ->
      contiguous_range_exact_lo (log (snd (nwState net h))) 0.
  Proof.
    intros.
    find_apply_lem_hyp lift_log_matching.
    unfold log_matching, log_matching_hosts in *.
    intuition.
    split.
    - intros.
      match goal with
        | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
          specialize (H h i);
            conclude H ltac:(simpl; repeat break_match; simpl in *; repeat find_rewrite; simpl in *;omega)
      end.
      break_exists_exists; intuition.
      simpl in *.
      repeat break_match; simpl in *; repeat find_rewrite; simpl in *; auto.
    - intros.
      cut (eIndex e > 0); intros; try omega.
      cut (In e (log (nwState (deghost net) h))); intros; eauto.
      simpl in *. repeat break_match. simpl in *. repeat find_rewrite. simpl in *. auto.
  Qed.
    
  
  Ltac start :=
    red; unfold leaderLogs_contiguous; intros;
    subst; simpl in *; find_higher_order_rewrite;
    update_destruct_hyp; subst; rewrite_update; eauto; simpl in *.

  Lemma leaderLogs_contiguous_init :
    refined_raft_net_invariant_init leaderLogs_contiguous.
  Proof.
    split; simpl in *; intuition.
  Qed.

  Lemma leaderLogs_contiguous_client_request :
    refined_raft_net_invariant_client_request leaderLogs_contiguous.
  Proof.
    start. 
    find_rewrite_lem update_elections_data_client_request_leaderLogs. eauto.
  Qed.

  Lemma leaderLogs_contiguous_timeout :
    refined_raft_net_invariant_timeout leaderLogs_contiguous.
  Proof.
    start.
    find_rewrite_lem update_elections_data_timeout_leaderLogs. eauto.
  Qed.

  Lemma leaderLogs_contiguous_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_contiguous.
  Proof.
    start.
    find_rewrite_lem update_elections_data_appendEntries_leaderLogs. eauto.
  Qed.

  Lemma leaderLogs_contiguous_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_contiguous.
  Proof.
    start. (* and finish *)
  Qed.
    

  Lemma leaderLogs_contiguous_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_contiguous.
  Proof.
    start.
    find_rewrite_lem update_elections_data_requestVote_leaderLogs. eauto.
  Qed.

  Lemma leaderLogs_contiguous_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_contiguous.
  Proof.
    start.
    match goal with
      | [ _ : context [ update_elections_data_requestVoteReply ?d ?s ?t ?v ?st ] |- _ ] =>
        pose proof update_elections_data_requestVoteReply_leaderLogs
             d s t v st
    end. intuition; repeat find_rewrite; eauto.
    simpl in *; break_or_hyp; eauto.
    find_inversion.
    eauto using logs_contiguous.
  Qed.

  Lemma leaderLogs_contiguous_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_contiguous.
  Proof.
    start. replace gd with (fst (nwState net h0)) in *; eauto.
    find_rewrite; reflexivity.
  Qed.

  Lemma leaderLogs_contiguous_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_contiguous.
  Proof.
    start. replace gd with (fst (nwState net h0)) in *; eauto.
    find_rewrite; reflexivity.
  Qed.

  Lemma leaderLogs_contiguous_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_contiguous.
  Proof.
    red. unfold leaderLogs_contiguous. intros.
    find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma leaderLogs_contiguous_reboot :
    refined_raft_net_invariant_reboot leaderLogs_contiguous.
  Proof.
    start. replace gd with (fst (nwState net h0)) in *; eauto.
    find_rewrite; reflexivity.
  Qed.

  Lemma leaderLogs_contiguous_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_contiguous net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_contiguous_init.
    - apply leaderLogs_contiguous_client_request.
    - apply leaderLogs_contiguous_timeout.
    - apply leaderLogs_contiguous_append_entries.
    - apply leaderLogs_contiguous_append_entries_reply.
    - apply leaderLogs_contiguous_request_vote.
    - apply leaderLogs_contiguous_request_vote_reply.
    - apply leaderLogs_contiguous_do_leader.
    - apply leaderLogs_contiguous_do_generic_server.
    - apply leaderLogs_contiguous_state_same_packet_subset.
    - apply leaderLogs_contiguous_reboot.
  Qed.

  Instance llci : leaderLogs_contiguous_interface : Prop.
  Proof.
    split.
    exact leaderLogs_contiguous_invariant.
  Qed.
End LeaderLogsContiguous.
