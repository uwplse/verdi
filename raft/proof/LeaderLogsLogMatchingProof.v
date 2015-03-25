Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LogMatchingInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import LeaderLogsSortedInterface.
Require Import SortedInterface.
Require Import LeaderLogsSublogInterface.
Require Import AllEntriesLeaderLogsInterface.

Require Import LeaderLogsLogMatchingInterface.

Section LeaderLogsLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lmi : log_matching_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {llsi : leaderLogs_sorted_interface}.
  Context {si : sorted_interface}.
  Context {aelli : all_entries_leader_logs_interface}.
  Context {llsli : leaderLogs_sublog_interface}.

  Lemma leaderLogs_entries_match_init :
    refined_raft_net_invariant_init leaderLogs_entries_match_host.
  Proof.
    unfold refined_raft_net_invariant_init, leaderLogs_entries_match_host.
    simpl.
    intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.


  Lemma update_elections_data_client_request_leaderLogs :
    forall h st client id c,
      leaderLogs (update_elections_data_client_request h st client id c) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_client_request in *.
    intros. repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma entries_match_cons_gt_maxTerm :
    forall x xs ys,
      sorted xs ->
      sorted ys ->
      eIndex x > maxIndex xs ->
      eTerm x > maxTerm ys ->
      entries_match xs ys ->
      entries_match (x :: xs) ys.
  Proof.
    unfold entries_match.
    intuition; simpl in *; intuition; subst; subst;
    try match goal with
        | [ H : In _ _ |- _ ] => apply maxTerm_is_max in H; [| solve[auto]]; omega
        | [ H : In _ _ |- _ ] => apply maxIndex_is_max in H; [| solve[auto]]; omega
      end.
    - match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
    - right. match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
  Qed.

  Lemma entries_match_cons_sublog :
    forall x xs ys,
      sorted xs ->
      sorted ys ->
      eIndex x > maxIndex xs ->
      entries_match xs ys ->
      (forall y, In y ys -> eTerm x = eTerm y -> In y xs) ->
      entries_match (x :: xs) ys.
  Proof.
    unfold entries_match.
    intuition; simpl in *; intuition; subst; subst;
    try solve [
         exfalso; try find_apply_hyp_hyp;
          match goal with
            | [ H : In _ _ |- _ ] => apply maxIndex_is_max in H; [| solve[auto]]; omega
          end].
    - match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
    - right. match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
  Qed.

  Lemma entries_match_nil :
    forall l,
      entries_match l [].
  Proof.
    red.
    simpl.
    intuition.
  Qed.

  Lemma lifted_logs_sorted :
    forall net h,
      refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    find_insterU. conclude_using eauto.
    unfold logs_sorted in *. break_and.
    unfold logs_sorted_host in *.
    find_insterU.
    find_rewrite_lem deghost_spec.
    eauto.
  Qed.

  Lemma leaderLogs_entries_match_client_request :
    refined_raft_net_invariant_client_request leaderLogs_entries_match_host.
  Proof.
    unfold refined_raft_net_invariant_client_request, leaderLogs_entries_match_host.
    simpl. intuition. subst. find_higher_order_rewrite.
    repeat update_destruct.
    - rewrite update_elections_data_client_request_leaderLogs in *.
      destruct (log d) using (handleClientRequest_log_ind $(eauto)$).
      + eauto.
      + destruct ll.
        * apply entries_match_nil.
        * { apply entries_match_cons_gt_maxTerm; eauto.
            - eauto using lifted_logs_sorted.
            - eapply leaderLogs_sorted_invariant; eauto.
            - omega.
            - find_copy_apply_lem_hyp leaderLogs_currentTerm_invariant; auto.
              find_copy_apply_lem_hyp leaderLogs_term_sanity_invariant.
              unfold leaderLogs_term_sanity in *.
              eapply_prop_hyp In In; simpl; eauto. repeat find_rewrite.
              simpl in *. omega.
          }
    - rewrite update_elections_data_client_request_leaderLogs in *.
      eauto.
    - destruct (log d) using (handleClientRequest_log_ind $(eauto)$).
      + eauto.
      + apply entries_match_cons_sublog; eauto.
        * eauto using lifted_logs_sorted.
        * eapply leaderLogs_sorted_invariant; eauto.
        * omega.
        * intros.
          eapply leaderLogs_sublog_invariant; eauto.
          simpl in *. congruence.
    - eauto.
  Qed.

  Lemma leaderLogs_entries_match_timeout :
    refined_raft_net_invariant_timeout leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_reboot :
    refined_raft_net_invariant_reboot leaderLogs_entries_match_host.
  Admitted.

  Lemma leaderLogs_entries_match_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_entries_match_host net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_entries_match_init.
    - apply leaderLogs_entries_match_client_request.
    - apply leaderLogs_entries_match_timeout.
    - apply leaderLogs_entries_match_append_entries.
    - apply leaderLogs_entries_match_append_entries_reply.
    - apply leaderLogs_entries_match_request_vote.
    - apply leaderLogs_entries_match_request_vote_reply.
    - apply leaderLogs_entries_match_do_leader.
    - apply leaderLogs_entries_match_do_generic_server.
    - apply leaderLogs_entries_match_state_same_packet_subset.
    - apply leaderLogs_entries_match_reboot.
  Qed.

  Instance lllmi : leaderLogs_entries_match_interface : Prop.
  Proof.
    split.
    exact leaderLogs_entries_match_invariant.
  Qed.
End LeaderLogsLogMatching.
