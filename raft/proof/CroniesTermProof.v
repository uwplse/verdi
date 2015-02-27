Require Import List.
Import ListNotations.
Require Import Arith.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CroniesTermInterface.

Section CroniesTermProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (@name_eq_dec _ _ y x)
    end.

  Lemma handleClientRequest_spec :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      currentTerm st' = currentTerm st.
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; intuition.
  Qed.

  Lemma cronies_term_client_request :
    refined_raft_net_invariant_client_request cronies_term.
  Proof.
    unfold refined_raft_net_invariant_client_request, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_apply_lem_hyp handleClientRequest_spec.
    find_rewrite. eauto.
  Qed.
  (*   H : handleTimeout h' (snd (nwState net h')) = (out, d, l)
       In h0 (cronies (update_elections_data_timeout h' (nwState net h')) t)
   *)

  Lemma handleTimeout_spec :
    forall h st out st' l t h',
      handleTimeout h (snd st) = (out, st', l) ->
      In h' (cronies (update_elections_data_timeout h st) t) ->
      (currentTerm (snd st) <= currentTerm st' /\
       (In h' (cronies (fst st) t) \/
        t = currentTerm st')).
  Proof.
    intros.
    unfold handleTimeout, tryToBecomeLeader, update_elections_data_timeout in *.
    repeat (break_match; repeat find_inversion; simpl in *; auto);
      intuition;
      unfold handleTimeout, tryToBecomeLeader in *;
      repeat (break_match; repeat find_inversion; simpl in *; auto); congruence.
  Qed.


  Lemma cronies_term_timeout :
    refined_raft_net_invariant_timeout cronies_term.
  Proof.
    unfold refined_raft_net_invariant_timeout, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    find_eapply_lem_hyp handleTimeout_spec; eauto. intuition.
    eapply le_trans; [|eauto]; eauto.
  Qed.

  Lemma doLeader_spec :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      currentTerm st' = currentTerm st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma cronies_term_do_leader :
    refined_raft_net_invariant_do_leader cronies_term.
  Proof.
    unfold refined_raft_net_invariant_do_leader, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    find_apply_lem_hyp doLeader_spec.
    repeat find_rewrite.
    match goal with
      | H : nwState ?net ?h = (?g, ?st) |- _ =>
        replace g with (fst (nwState net h)) in *; [|rewrite H; auto];
        replace st with (snd (nwState net h)) in *; [|rewrite H; auto]
    end; eauto.
  Qed.

  Lemma doGenericServer_spec :
    forall st h os st' ms,
      doGenericServer h st = (os, st', ms) ->
      currentTerm st' = currentTerm st.
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; repeat find_inversion;
    use_applyEntries_spec; subst; simpl in *;
    auto.
  Qed.

  Lemma cronies_term_do_generic_server :
    refined_raft_net_invariant_do_generic_server cronies_term.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    find_apply_lem_hyp doGenericServer_spec.
    repeat find_rewrite.
    match goal with
      | H : nwState ?net ?h = (?g, ?st) |- _ =>
        replace g with (fst (nwState net h)) in *; [|rewrite H; auto];
        replace st with (snd (nwState net h)) in *; [|rewrite H; auto]
    end; eauto.
  Qed.

  Lemma handleAppendEntries_spec :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      currentTerm st <= currentTerm st'.
  Proof.
    intros.
    unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *;
    do_bool; auto.
  Qed.

  Lemma update_elections_data_appendEntries_spec :
    forall h st t n pli plt es ci st' e t',
      update_elections_data_appendEntries h st t n pli plt es ci = st' ->
      In e (cronies st' t') ->
      In e (cronies (fst st) t').
  Proof.
    intros.
    unfold update_elections_data_appendEntries in *.
    repeat break_match; repeat find_rewrite; subst; simpl in *; auto.
  Qed.

  Lemma cronies_term_append_entries :
    refined_raft_net_invariant_append_entries cronies_term.
  Proof.
    unfold refined_raft_net_invariant_append_entries, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    find_apply_lem_hyp handleAppendEntries_spec.
    find_eapply_lem_hyp update_elections_data_appendEntries_spec; eauto.
    eapply le_trans; [|eauto]; eauto.
  Qed.

  Lemma handleAppendEntriesReply_spec :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      currentTerm st <= currentTerm st'.
  Proof.
    intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *;
    do_bool; intuition.
  Qed.


  Lemma cronies_term_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply cronies_term.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    find_apply_lem_hyp handleAppendEntriesReply_spec.
    eapply le_trans; [|eauto]; eauto.
  Qed.

  Lemma handleRequestVote_spec :
    forall h st t h' pli plt st' m,
      handleRequestVote h st t h' pli plt = (st', m) ->
      currentTerm st <= currentTerm st'.
  Proof.
    intros.
    unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *;
    do_bool; intuition.
  Qed.

  Lemma update_elections_data_requestVote_spec :
    forall h st t h' pli plt st' t' e s,
      update_elections_data_requestVote h h' t pli plt s st = st' ->
      In e (cronies st' t') ->
      In e (cronies (fst st) t').
  Proof.
    intros.
    unfold update_elections_data_requestVote in *.
    repeat break_match; repeat find_rewrite; subst; simpl in *; auto.
  Qed.

  Lemma cronies_term_request_vote :
    refined_raft_net_invariant_request_vote cronies_term.
  Proof.
    unfold refined_raft_net_invariant_request_vote, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    find_apply_lem_hyp handleRequestVote_spec.
    find_eapply_lem_hyp update_elections_data_requestVote_spec; eauto.
    eapply le_trans; [|eauto]; eauto.
  Qed.


  Lemma handleRequestVoteReply_spec :
    forall h st h' t v st',
      st' = handleRequestVoteReply h st h' t v ->
      currentTerm st' = currentTerm st \/
      (currentTerm st <= currentTerm st' /\
       type st' = Follower).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition.
  Qed.


  Lemma cronies_term_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply cronies_term.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, cronies_term.
    intros. subst. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
    match goal with
      | H : forall _, st' _ = _ |- _ => clear H
    end.
    unfold update_elections_data_requestVoteReply in *.
    match goal with
      | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?v] =>
        remember (handleRequestVoteReply h st h' t v) as new_state
    end.
    find_copy_apply_lem_hyp handleRequestVoteReply_spec.
    intuition.
    - unfold update_elections_data_requestVoteReply in *.
      break_match; simpl in *; repeat find_rewrite; eauto;
      break_match; eauto;
      subst; repeat find_reverse_rewrite; intuition.
    - unfold update_elections_data_requestVoteReply in *.
      break_match; simpl in *;
      try solve [subst; unfold raft_data in *; congruence].
      eapply le_trans; [|eauto]; eauto.
  Qed.

  Lemma cronies_term_init :
    refined_raft_net_invariant_init cronies_term.
  Proof.
    unfold refined_raft_net_invariant_init, cronies_term.
    intros. simpl in *. intuition.
  Qed.

  Lemma cronies_term_reboot :
    refined_raft_net_invariant_reboot cronies_term.
  Proof.
    unfold refined_raft_net_invariant_reboot, cronies_term, reboot.
    intros. simpl in *. repeat find_higher_order_rewrite.
    update_destruct; subst; rewrite_update; eauto.
    simpl in *.
     match goal with
      | H : nwState ?net ?h = (?g, ?st) |- _ =>
        replace g with (fst (nwState net h)) in *; [|rewrite H; auto];
        replace st with (snd (nwState net h)) in *; [|rewrite H; auto]
     end; eauto.
  Qed.

  Lemma cronies_term_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset cronies_term.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, cronies_term.
    intros.
    repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Theorem cronies_term_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      cronies_term net.
  Proof.
    intros. apply refined_raft_net_invariant; auto.
    - apply cronies_term_init.
    - apply cronies_term_client_request.
    - apply cronies_term_timeout.
    - apply cronies_term_append_entries.
    - apply cronies_term_append_entries_reply.
    - apply cronies_term_request_vote.
    - apply cronies_term_request_vote_reply.
    - apply cronies_term_do_leader.
    - apply cronies_term_do_generic_server.
    - apply cronies_term_state_same_packet_subset.
    - apply cronies_term_reboot.
  Qed.

  Instance cti : cronies_term_interface.
  Proof.
    split.
    auto using cronies_term_invariant.
  Qed.
End CroniesTermProof.
