Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Sumbool.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.
Require Import AllEntriesLeaderLogsInterface.
Require Import PrefixWithinTermInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import LeaderLogsPreservedInterface.
Require Import EveryEntryWasCreatedInterface.
Require Import LeaderLogsVotesWithLogInterface.
Require Import AllEntriesVotesWithLogInterface.
Require Import VotesWithLogSortedInterface.
Require Import TermsAndIndicesFromOneInterface.

Section LeaderCompleteness.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {aelli : all_entries_leader_logs_interface}.
  
  Context {pwti : prefix_within_term_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {llpi : leaderLogs_preserved_interface}.
  Context {eewci : every_entry_was_created_interface}.
  Context {llvwli : leaderLogs_votesWithLog_interface}.
  Context {aevwli : allEntries_votesWithLog_interface}.
  Context {vwlsi : votesWithLog_sorted_interface}.
  Context {taifoi : terms_and_indices_from_one_interface}.

  Fixpoint contradicting_leader_logs_on_leader l t e :=
    match l with
      | (t', log') :: l' =>
        if (sumbool_and _ _ _ _
                        (lt_dec t t')
                        (sumbool_not _ _
                                     (in_dec entry_eq_dec e log'))) then
          (t', log') :: contradicting_leader_logs_on_leader l' t e
        else
          contradicting_leader_logs_on_leader l' t e
      | [] => []
    end.
  
  Fixpoint contradicting_leader_logs net nodes t e : list (term * name * list entry) :=
    match nodes with
      | h :: nodes' => (map (fun l => (fst l, h, snd l))
                           (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e))
                        ++ contradicting_leader_logs net nodes' t e
      | [] => []
    end.

  Definition minimal_contradicting_leader_log net t e :=
    argmin (fun l => fst (fst l)) (contradicting_leader_logs net nodes t e).

  Lemma contradicting_leader_logs_on_leader_empty :
    forall l t e,
      contradicting_leader_logs_on_leader l t e = [] ->
      forall t' log,
        In (t', log) l ->
        t' > t ->
        In e log.
  Proof.
    induction l; intros; simpl in *; intuition; subst;
    repeat break_match; subst; simpl in *; intuition eauto;
    congruence.
  Qed.

  Lemma contradicting_leader_logs_empty :
    forall net nodes t e,
      contradicting_leader_logs net nodes t e = [] ->
      forall h,
        In h nodes ->
        contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e = [].
  Proof.
    intros.
    induction nodes; simpl in *; intuition; subst;
    find_apply_lem_hyp app_eq_nil; intuition;
    find_apply_lem_hyp map_eq_nil; auto.
  Qed.

  Lemma minimal_contradicting_leader_log_None :
    forall net t e,
      minimal_contradicting_leader_log net t e = None ->
      forall t' log h,
        In (t', log) (leaderLogs (fst (nwState net h))) ->
        t' > t ->
        In e log.
  Proof.
    intros.
    find_apply_lem_hyp argmin_None.
    eapply contradicting_leader_logs_on_leader_empty; eauto.
    eapply contradicting_leader_logs_empty; eauto.
    apply all_fin_all.
  Qed.

  Lemma In_contradicting_logs_on_leader_elim :
    forall l t e t' l',
      In (t', l') (contradicting_leader_logs_on_leader l t e) ->
      In (t', l') l /\ t < t' /\ ~ In e l'.
  Proof.
    intros; induction l; simpl in *; intuition;
    repeat break_match; subst; simpl in *; intuition;
    find_inversion; intuition.
  Qed.

  Lemma in_contradicting_leader_logs :
    forall net nodes t e t' h l,
      In (t', h, l) (contradicting_leader_logs net nodes t e) ->
      In (t', l) (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e).
  Proof.
    induction nodes; intros; simpl in *; intuition.
    do_in_app. intuition.
    do_in_map. find_inversion. rewrite <- surjective_pairing. auto.
  Qed.

  Lemma in_contradicting_leader_logs_on_leader_in_leaderLog :
    forall ll t e t' l,
      In (t', l) (contradicting_leader_logs_on_leader ll t e) ->
      In (t', l) ll.
  Proof.
    induction ll; intros; simpl in *; intuition.
    repeat break_match; simpl in *; intuition eauto.
  Qed.

  Lemma in_contradicting_leader_logs_on_leader_not_in_log :
    forall t' l ll t e,
      In (t', l) (contradicting_leader_logs_on_leader ll t e) ->
      In e l -> False.
  Proof.
    induction ll; intros; simpl in *; intuition.
    repeat break_match; simpl in *; intuition eauto.
    find_inversion. auto.
  Qed.

  Lemma in_contradicting_leader_logs_on_leader_term_lt :
    forall t' l ll t e,
      In (t', l) (contradicting_leader_logs_on_leader ll t e) ->
      t < t'.
  Proof.
    induction ll; intros; simpl in *; intuition.
    repeat break_match; simpl in *; intuition; repeat find_inversion; eauto.
  Qed.

  Lemma contradicting_leader_logs_on_leader_complete :
    forall t e t' l ll,
      In (t', l) ll ->
      t < t' ->
      ~ In e l ->
      In (t', l) (contradicting_leader_logs_on_leader ll t e).
  Proof.
    induction ll; intros; simpl in *; intuition;
    repeat break_match; repeat find_inversion; simpl in *; intuition.
  Qed.

  Lemma contradicting_leader_logs_complete :
    forall net nodes h t e l t',
      In h nodes ->
      In (t', l) (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e) ->
      In (t', h, l) (contradicting_leader_logs net nodes t e).
  Proof.
    induction nodes; intros; simpl in *; intuition.
    apply in_or_app.
    subst. left. apply in_map_iff. eexists. intuition eauto. simpl. auto.
  Qed.

  Lemma minimal_contradicting_leader_log_elim :
    forall net t e t' h l,
      minimal_contradicting_leader_log net t e = Some (t', h, l) ->

      (t < t' /\
       In (t', l) (leaderLogs (fst (nwState net h))) /\
       ~ In e l /\
       (forall h' t'' l',
          In (t'', l') (leaderLogs (fst (nwState net h'))) ->
          (t'' <= t \/
           t'' >= t' \/
           In e l'))).
  Proof.
    unfold minimal_contradicting_leader_log.
    intros.
    find_apply_lem_hyp argmin_elim. intuition.
    - eauto using in_contradicting_leader_logs_on_leader_term_lt,
                  in_contradicting_leader_logs.
    - eauto using in_contradicting_leader_logs,
                  in_contradicting_leader_logs_on_leader_in_leaderLog.
    - eauto using in_contradicting_leader_logs,
                  in_contradicting_leader_logs_on_leader_not_in_log.
    - destruct (le_lt_dec t'' t); auto.
      destruct (le_lt_dec t' t''); auto.
      destruct (in_dec entry_eq_dec e l'); auto.
      find_eapply_lem_hyp contradicting_leader_logs_on_leader_complete; eauto.
      find_eapply_lem_hyp contradicting_leader_logs_complete; [|solve [apply all_fin_all]].
      find_apply_hyp_hyp. simpl in *. omega.
  Qed.

  Lemma maxTerm_zero_or_entry :
    forall l,
      maxTerm l = 0 \/ exists e, In e l /\ eTerm e = maxTerm l.
  Proof.
    destruct l; simpl; eauto.
  Qed.

  Lemma maxIndex_zero_or_entry :
    forall l,
      maxIndex l = 0 \/ exists e, In e l /\ eIndex e = maxIndex l.
  Proof.
    destruct l; simpl; eauto.
  Qed.

  Theorem leader_completeness_directly_committed_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_completeness_directly_committed net.
  Proof.
    unfold leader_completeness_directly_committed in *.
    intros.
    unfold directly_committed in *.
    destruct (minimal_contradicting_leader_log net (eTerm e) e) eqn:?;
             eauto using minimal_contradicting_leader_log_None.

    repeat destruct p.
  
    find_apply_lem_hyp minimal_contradicting_leader_log_elim.
    match goal with
      | [ H : exists _, _ |- _ ] => destruct H as [quorum]
    end.
    intuition.
    destruct (le_lt_dec n t).
    - exfalso.
      assert (forall e', In e' l -> (eTerm e' < eTerm e) \/ (eTerm e' = eTerm e /\ eIndex e' < eIndex e)).
      {
        intros.
        destruct (lt_eq_lt_dec (eTerm e') (eTerm e)).
        - intuition. destruct (le_lt_dec (eIndex e) (eIndex e')); auto.
          assert (exists x, In x quorum).
          {
            destruct quorum.
            - simpl in *. omega.
            - simpl. eauto.
          }

          break_exists.
          assert (prefix_within_term (map snd (allEntries (fst (nwState net x)))) l) by eauto using prefix_within_term_invariant.
          unfold prefix_within_term in *.
          exfalso.
          find_false.
          match goal with
            | [ H : _ |- _ ] => eapply H; try eassumption; auto;
                                [apply in_map_iff; eexists; split; [|eauto]; auto]
          end.
        - assert (leaderLogs_term_sanity net) by eauto using leaderLogs_term_sanity_invariant.
          unfold leaderLogs_term_sanity in *.
          assert (eTerm e' < n) by eauto.
          assert (every_entry_was_created net) by eauto using every_entry_was_created_invariant.
          unfold every_entry_was_created in *.
          find_insterU. find_insterU. find_insterU. find_insterU.
          conclude_using eauto.
          conclude_using eauto.
          break_exists.
          find_copy_apply_hyp_hyp. repeat break_or_hyp; try omega.
          assert (leaderLogs_preserved net) by eauto using leaderLogs_preserved_invariant.
          unfold leaderLogs_preserved in *.
          exfalso. eauto.
      }

      assert (leaderLogs_votesWithLog net) by eauto using leaderLogs_votesWithLog_invariant.
      unfold leaderLogs_votesWithLog in *.
      find_apply_hyp_hyp.
      match goal with
        | [ H : exists _, _ |- _ ] => destruct H as [quorum']
      end.
      break_and.

      assert (NoDup nodes) by eauto using all_fin_NoDup.
      match goal with
        | H : NoDup nodes, _ : NoDup ?l1, _ : NoDup ?l2 |- _ =>
          eapply pigeon with (l := nodes) (sub1 := l1) (sub2 := l2) in H
      end; eauto using all_fin_all, name_eq_dec, div2_correct.

      match goal with
        | [ H : exists _, _ |- _ ] => destruct H as [a]
      end.
      break_and.
      find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      break_exists. break_and.
      assert (In e x).
      {
        assert (allEntries_votesWithLog net) by eauto using allEntries_votesWithLog_invariant.
        unfold allEntries_votesWithLog in *.
        eapply_prop_hyp In In; eauto.
        break_or_hyp; auto.
        break_exists. break_and.
        match goal with
          | [ H : context [ In _ _ -> _ \/ _ ],
              H' : In _ _ |- _ ] =>
            eapply H in H'
        end.
        repeat (try break_or_hyp; break_and); try omega.
        congruence.
      }

      assert (sorted x) by (eapply votesWithLog_sorted_invariant; eauto).

      assert (maxTerm x >= eTerm e) by eauto using maxTerm_is_max.
      assert (maxIndex x >= eIndex e) by eauto using maxIndex_is_max.
      assert (exists e', In e' l /\
                         eTerm e' = maxTerm l /\
                         eIndex e' = maxIndex l).
      {
        assert (eTerm e >= 1 /\ eIndex e >= 1) by (eapply terms_and_indices_from_one_invariant; eauto).
        destruct l.
        - simpl in *.
          unfold moreUpToDate in *. do_bool.
          repeat (intuition; do_bool); try omega.
        - simpl in *. eauto.
      }

      match goal with
        | [ H : exists _, _ |- _ ] => destruct H as [e']
      end.
      break_and.

      find_apply_hyp_hyp.

      unfold moreUpToDate in *.
      do_bool; repeat (try break_or_hyp; break_and; do_bool); omega.
    - match goal with
        | [ H : context [In], H' : context [In] |- _ ] => apply H in H'; intuition; omega
      end.
  Qed.

  Lemma leader_completeness_init :
    refined_raft_net_invariant_init leader_completeness.
  Admitted.

  Lemma leader_completeness_client_request :
    refined_raft_net_invariant_client_request leader_completeness.
  Admitted.

  Lemma leader_completeness_timeout :
    refined_raft_net_invariant_timeout leader_completeness.
  Admitted.

  Lemma leader_completeness_append_entries :
    refined_raft_net_invariant_append_entries leader_completeness.
  Admitted.

  Lemma leader_completeness_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leader_completeness.
  Admitted.

  Lemma leader_completeness_request_vote :
    refined_raft_net_invariant_request_vote leader_completeness.
  Admitted.

  Lemma leader_completeness_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leader_completeness.
  Admitted.

  Lemma leader_completeness_do_leader :
    refined_raft_net_invariant_do_leader leader_completeness.
  Admitted.

  Lemma leader_completeness_do_generic_server :
    refined_raft_net_invariant_do_generic_server leader_completeness.
  Admitted.

  Lemma leader_completeness_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leader_completeness.
  Admitted.

  Lemma leader_completeness_reboot :
    refined_raft_net_invariant_reboot leader_completeness.
  Admitted.

  Theorem leader_completeness_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_completeness net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leader_completeness_init.
    - apply leader_completeness_client_request.
    - apply leader_completeness_timeout.
    - apply leader_completeness_append_entries.
    - apply leader_completeness_append_entries_reply.
    - apply leader_completeness_request_vote.
    - apply leader_completeness_request_vote_reply.
    - apply leader_completeness_do_leader.
    - apply leader_completeness_do_generic_server.
    - apply leader_completeness_state_same_packet_subset.
    - apply leader_completeness_reboot.
  Qed.

  Instance lci :  leader_completeness_interface.
  Proof.
    split.
    exact leader_completeness_invariant.
  Qed.
End LeaderCompleteness.
