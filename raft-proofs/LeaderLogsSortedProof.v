Require Import GhostSimulations.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import SpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import LeaderLogsSortedInterface.
Require Import SortedInterface.


Section LeaderLogsSorted.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {si : sorted_interface}.

  Lemma leaderLogs_sorted_init :
    refined_raft_net_invariant_init leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_init, leaderLogs_sorted.
    intros. subst. simpl in *. intuition.
  Qed.

  Lemma leaderLogs_update_elections_data_client_request :
    forall me st client id c,
      leaderLogs (update_elections_data_client_request me st client id c) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_client_request.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma leaderLogs_sorted_client_request :
    refined_raft_net_invariant_client_request leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_client_request, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify; simpl in *.
    - rewrite leaderLogs_update_elections_data_client_request in *.
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

  Lemma leaderLogs_update_elections_data_timeout :
    forall h st,
      leaderLogs (update_elections_data_timeout h st) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; simpl in *; auto.
  Qed.

  Lemma leaderLogs_sorted_timeout :
    refined_raft_net_invariant_timeout leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_timeout, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify; simpl in *;
    try rewrite leaderLogs_update_elections_data_timeout in *;
    eauto.
  Qed.

  Lemma leaderLogs_update_elections_data_AE :
    forall me st t li pli plt es lci,
      leaderLogs (update_elections_data_appendEntries me st t li pli plt es lci) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_appendEntries.
    intros.
    repeat break_match; subst; auto.
  Qed.

  Lemma leaderLogs_sorted_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_append_entries, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify; simpl in *.
    - rewrite leaderLogs_update_elections_data_AE in *.
      eauto.
    - eauto.
  Qed.

  Lemma leaderLogs_sorted_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify; simpl in *; eauto.
  Qed.

  Lemma leaderLogs_sorted_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_request_vote, leaderLogs_sorted.
    intros.
    subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify.
    - unfold update_elections_data_requestVote in *.
      repeat break_match; simpl in *; intuition; repeat find_inversion; eauto.
    - eauto.
  Qed.


  Lemma leaderLogs_update_elections_data_request_vote_reply :
    forall {h st h' t r st'},
      handleRequestVoteReply h (snd st) h' t r = st' ->
      forall (P : list (term * list entry) -> Prop),
        (forall t, P ((t, log (snd st)) :: leaderLogs (fst st))) ->
        (P (leaderLogs (fst st))) ->
        (P (leaderLogs (update_elections_data_requestVoteReply h h' t r st))).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; simpl in *; eauto.
    repeat find_rewrite.
    match goal with
      | H : handleRequestVoteReply _ _ _ _ _ = _ |- _ =>
        symmetry in H
    end.
    find_apply_lem_hyp handleRequestVoteReply_spec.
    intuition; repeat find_rewrite; auto.
  Qed.
  
  Lemma leaderLogs_sorted_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify; eauto.
    match goal with
      | _ : context [ leaderLogs (update_elections_data_requestVoteReply ?h ?s ?t ?v ?st) ] |- _ =>
        destruct (leaderLogs (update_elections_data_requestVoteReply h s t v st))
                 using (leaderLogs_update_elections_data_request_vote_reply ltac:(eauto))
    end; eauto.
    simpl in *. intuition eauto.
    find_inversion. eauto using sorted_host_lifted.
  Qed.

  Lemma leaderLogs_sorted_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_do_leader, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify.
    - match goal with
        | [ H : _, H' : _ |- _ ] =>
          eapply H; rewrite H'; simpl; eauto
      end.
    - eauto.
  Qed.

  Lemma leaderLogs_sorted_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, leaderLogs_sorted.
    intros. subst. simpl in *. find_higher_order_rewrite.
    update_destruct_simplify.
    - match goal with
        | [ H : _, H' : _ |- _ ] =>
          eapply H; rewrite H'; simpl; eauto
      end.
    - eauto.
  Qed.

  Lemma leaderLogs_sorted_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, leaderLogs_sorted.
    intros. subst. simpl in *. find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma leaderLogs_sorted_reboot :
    refined_raft_net_invariant_reboot leaderLogs_sorted.
  Proof.
    unfold refined_raft_net_invariant_reboot, leaderLogs_sorted.
    intros.
    find_higher_order_rewrite.
    update_destruct_simplify.
    - match goal with
        | [ H : _, H' : _ |- _ ] =>
          eapply H; rewrite H'; simpl; eauto
      end.
    - eauto.
  Qed.

  Lemma leaderLogs_sorted_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_sorted net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_sorted_init.
    - apply leaderLogs_sorted_client_request.
    - apply leaderLogs_sorted_timeout.
    - apply leaderLogs_sorted_append_entries.
    - apply leaderLogs_sorted_append_entries_reply.
    - apply leaderLogs_sorted_request_vote.
    - apply leaderLogs_sorted_request_vote_reply.
    - apply leaderLogs_sorted_do_leader.
    - apply leaderLogs_sorted_do_generic_server.
    - apply leaderLogs_sorted_state_same_packet_subset.
    - apply leaderLogs_sorted_reboot.
  Qed.

  Instance llsi : leaderLogs_sorted_interface.
  Proof.
    split.
    eauto using leaderLogs_sorted_invariant.
  Defined.
End LeaderLogsSorted.
