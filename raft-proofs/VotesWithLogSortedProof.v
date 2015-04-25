Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import VotesWithLogSortedInterface.
Require Import SortedInterface.

Section VotesWithLogSorted.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {si : sorted_interface}.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma votesWithLog_sorted_init :
    refined_raft_net_invariant_init votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_init, votesWithLog_sorted.
    intros. subst. simpl in *. intuition.
  Qed.

  Lemma votesWithLog_update_elections_data_client_request :
    forall me st client id c,
      votesWithLog (update_elections_data_client_request me st client id c) =
      votesWithLog (fst st).
  Proof.
    unfold update_elections_data_client_request.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma votesWithLog_sorted_client_request :
    refined_raft_net_invariant_client_request votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_client_request, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct; simpl in *.
    - rewrite votesWithLog_update_elections_data_client_request in *.
      eauto.
    - eauto.
  Qed.

  Lemma sorted_host_lifted :
    forall net h,
      refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    find_insterU. conclude_using eauto.
    unfold logs_sorted, logs_sorted_host in *. break_and.
    unfold deghost in *. simpl in *. break_match. eauto.
  Qed.

  Lemma votesWithLog_update_elections_data_timeout :
    forall {h st out st' l},
      handleTimeout h (snd st) = (out, st', l) ->
      forall (P : list (term * name * list entry) -> Prop),
        (forall t cid, P ((t, cid, log st') :: votesWithLog (fst st))) ->
        (P (votesWithLog (fst st))) ->
        (P (votesWithLog (update_elections_data_timeout h st))).
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; simpl in *; find_inversion; eauto.
  Qed.

  Lemma votesWithLog_sorted_timeout :
    refined_raft_net_invariant_timeout votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_timeout, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct; simpl in *.
    - destruct (votesWithLog (update_elections_data_timeout h0 (nwState net h0)))
               using (votesWithLog_update_elections_data_timeout $(eauto)$).
      + simpl in *. intuition.
        * find_inversion. erewrite handleTimeout_log_same by eauto.
          eauto using sorted_host_lifted.
        * eauto.
      + eauto.
    - eauto.
  Qed.

  Lemma votesWithLog_update_elections_data_AE :
    forall me st t li pli plt es lci,
      votesWithLog (update_elections_data_appendEntries me st t li pli plt es lci) =
      votesWithLog (fst st).
  Proof.
    unfold update_elections_data_appendEntries.
    intros.
    repeat break_match; subst; auto.
  Qed.

  Lemma votesWithLog_sorted_append_entries :
    refined_raft_net_invariant_append_entries votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_append_entries, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct; simpl in *.
    - rewrite votesWithLog_update_elections_data_AE in *.
      eauto.
    - eauto.
  Qed.

  Lemma votesWithLog_sorted_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct; simpl in *; eauto.
  Qed.

  Lemma votesWithLog_sorted_request_vote :
    refined_raft_net_invariant_request_vote votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_request_vote, votesWithLog_sorted.
    intros.
    subst. simpl in *. find_higher_order_rewrite.
    update_destruct.
    - unfold update_elections_data_requestVote in *.
      repeat break_match; simpl in *; intuition; repeat find_inversion; eauto.
      erewrite handleRequestVote_log; eauto.
      eauto using sorted_host_lifted.
    - eauto.
  Qed.

  Lemma votesWithLog_update_elections_data_RVR :
    forall me src t status st,
      votesWithLog (update_elections_data_requestVoteReply me src t status st) =
      votesWithLog (fst st).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; simpl; auto.
  Qed.

  Lemma votesWithLog_sorted_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct.
    - rewrite votesWithLog_update_elections_data_RVR in *.
      eauto.
    - eauto.
  Qed.

  Lemma votesWithLog_sorted_do_leader :
    refined_raft_net_invariant_do_leader votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_do_leader, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct.
    - match goal with
        | [ H : _, H' : _ |- _ ] =>
          eapply H; rewrite H'; simpl; eauto
      end.
    - eauto.
  Qed.

  Lemma votesWithLog_sorted_do_generic_server :
    refined_raft_net_invariant_do_generic_server votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, votesWithLog_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct.
    - match goal with
        | [ H : _, H' : _ |- _ ] =>
          eapply H; rewrite H'; simpl; eauto
      end.
    - eauto.
  Qed.

  Lemma votesWithLog_sorted_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, votesWithLog_sorted.
    intros. subst. simpl in *. find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma votesWithLog_sorted_reboot :
    refined_raft_net_invariant_reboot votesWithLog_sorted.
  Proof.
    unfold refined_raft_net_invariant_reboot, votesWithLog_sorted.
    intros.
    find_higher_order_rewrite.
    update_destruct.
    - match goal with
        | [ H : _, H' : _ |- _ ] =>
          eapply H; rewrite H'; simpl; eauto
      end.
    - eauto.
  Qed.

  Lemma votesWithLog_sorted_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      votesWithLog_sorted net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply votesWithLog_sorted_init.
    - apply votesWithLog_sorted_client_request.
    - apply votesWithLog_sorted_timeout.
    - apply votesWithLog_sorted_append_entries.
    - apply votesWithLog_sorted_append_entries_reply.
    - apply votesWithLog_sorted_request_vote.
    - apply votesWithLog_sorted_request_vote_reply.
    - apply votesWithLog_sorted_do_leader.
    - apply votesWithLog_sorted_do_generic_server.
    - apply votesWithLog_sorted_state_same_packet_subset.
    - apply votesWithLog_sorted_reboot.
  Qed.

  Instance vwlsi : votesWithLog_sorted_interface.
  Proof.
    split.
    exact votesWithLog_sorted_invariant.
  Qed.
End VotesWithLogSorted.
