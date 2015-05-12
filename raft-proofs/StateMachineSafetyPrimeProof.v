Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import CommonTheorems.
Require Import Raft.
Require Import SortedInterface.
Require Import RaftRefinementInterface.
Require Import StateMachineSafetyPrimeInterface.
Require Import LeaderCompletenessInterface.
Require Import LeaderLogsContiguousInterface.
Require Import AllEntriesLeaderLogsInterface.
Require Import LogMatchingInterface.
Require Import UniqueIndicesInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import LeaderLogsSortedInterface.
Require Import LeaderLogsLogMatchingInterface.
Require Import LogsLeaderLogsInterface.
Require Import OneLeaderLogPerTermInterface.
Require Import RefinedLogMatchingLemmasInterface.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section StateMachineSafety'.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lci : leader_completeness_interface}.
  Context {aelli : all_entries_leader_logs_interface}.
  Context {lmi : log_matching_interface}.
  Context {uii : unique_indices_interface}.
  Context {aerlli : append_entries_leaderLogs_interface}.
  Context {llsi : leaderLogs_sorted_interface}.
  Context {lsi : sorted_interface}.
  Context {llci : leaderLogs_contiguous_interface}.
  Context {lllmi : leaderLogs_entries_match_interface}.
  Context {llli : logs_leaderLogs_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.

  
  Theorem lift_log_matching :
    forall net,
      refined_raft_intermediate_reachable net ->
      log_matching (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using log_matching_invariant.
  Qed.

  Theorem lift_sorted :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_sorted (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using logs_sorted_invariant.
  Qed.

  Theorem lift_entries_match :
    forall net h h',
      refined_raft_intermediate_reachable net ->
      entries_match (log (snd (nwState net h))) (log (snd (nwState net h'))).
  Proof.
    intros.
    find_apply_lem_hyp lift_log_matching.
    unfold log_matching, log_matching_hosts in *. intuition.
    unfold deghost in *. simpl in *.
    repeat break_match; eauto.
  Qed.

  Theorem lift_UniqueIndices :
    forall net,
      refined_raft_intermediate_reachable net ->
      UniqueIndices (deghost net).
  Proof.
    intros. eapply lift_prop; eauto using UniqueIndices_invariant.
  Qed.

  Theorem lift_uniqueIndices_log :
    forall net h,
      refined_raft_intermediate_reachable net ->
      uniqueIndices (log (snd (nwState net h))).
  Proof.
    intros.
    find_apply_lem_hyp lift_UniqueIndices.
    unfold UniqueIndices, uniqueIndices_host_invariant in *.
    intuition.
    unfold deghost in *. simpl in *. break_match; eauto.
  Qed.

  Theorem lift_logs_sorted :
    forall net h,
      refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    find_apply_lem_hyp lift_sorted.
    unfold logs_sorted, logs_sorted_host in *.
    intuition.
    unfold deghost in *. simpl in *. break_match; eauto.
  Qed.
  
  Theorem state_machine_safety_host'_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      state_machine_safety_host' net.
  Proof.
    unfold state_machine_safety_host'. intros.
    find_copy_apply_lem_hyp leader_completeness_invariant.
    unfold leader_completeness in *. intuition.
    unfold committed in *. break_exists. intuition.
    repeat match goal with
             | [ H : directly_committed _ ?e |- _ ] =>
               try match goal with
                     | H' : context [ allEntries ] |- _ =>
                       match type of H' with
                         | context [ e ] => fail 3
                       end
                   end;
                 let Hnew := fresh "H" in
                 remember H as Hnew; unfold directly_committed in Hnew;
                 match goal with
                   | [ Heq : Hnew = H |- _ ] => clear Heq
                 end
           end.
    break_exists. intuition.
    assert (NoDup nodes) by eauto using all_fin_NoDup.
    match goal with
      | H : NoDup nodes, _ : NoDup ?l1, _ : NoDup ?l2 |- _ =>
        eapply pigeon with (l := nodes) (sub1 := l1) (sub2 := l2) in H
    end; eauto using all_fin_all, name_eq_dec, div2_correct.
    break_exists.
    intuition.
    repeat find_apply_hyp_hyp.
    do 2 find_apply_lem_hyp all_entries_leader_logs_invariant; auto.
    intuition; try solve [break_exists; intuition; find_false; eauto].
    match goal with
      | [ _ : eIndex ?e <= eIndex ?x, _ : eIndex ?e' <= eIndex ?x',
          _ : In ?x ?l |- ?e = ?e' ] =>
        cut (In e l /\ In e' l)
    end;
      [intros; intuition;
       eapply uniqueIndices_elim_eq;
       eauto using lift_uniqueIndices_log|].
    intuition;
      match goal with
        | _ : In ?e ?l, _ : eIndex ?e <= eIndex ?x, _ : In ?x ?l' |- In ?e ?l' =>
          assert (entries_match l l') as Hem by eauto using lift_entries_match;
            specialize (Hem x x e)
      end; intuition.
  Qed.


  Ltac copy_eapply_prop_hyp P Q :=
    match goal with
      | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
        copy_eapply H H'
    end.

  Lemma entries_contiguous :
    forall net p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      contiguous_range_exact_lo es pli.
  Proof. (* by log matching, annoying because of refinement *)
  Admitted.

  Lemma exists_deghosted_packet :
    forall net (p : packet (params := raft_refined_multi_params (raft_params := raft_params))),
      In p (nwPackets net) ->
      exists q,
        In q (nwPackets (deghost net)) /\ q = deghost_packet p.
  Proof.
    unfold deghost.
    simpl.
    intros.
    eexists; intuition eauto.
    apply in_map_iff. eexists; eauto.
  Qed.
  
  Lemma network_host_entries :
    forall net p t n pli plt es ci h e e',
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e (log (snd (nwState net h))) ->
      In e' es ->
      eIndex e = eIndex e' ->
      eTerm e = eTerm e' ->
      In e es.
  Proof.
    intros.
    pose proof lift_uniqueIndices_log net h; intuition.
    find_copy_apply_lem_hyp lift_log_matching.
    unfold log_matching, log_matching_nw in *.
    intuition.
    find_apply_lem_hyp exists_deghosted_packet.
    break_exists.
    intuition.
    subst. destruct p; simpl in *; subst.
    eapply_prop_hyp In In; simpl; eauto. intuition.
    match goal with
      | H : forall _ _ _, _ |- _ =>
        specialize (H h e' e)
    end; intuition.
    repeat break_match. simpl in *. repeat find_rewrite. simpl in *.
    intuition.
    match goal with
      | H : forall _, _ <= _ -> _ |- _ =>
        specialize (H e'); conclude H ltac:(omega)
    end. intuition.
    eapply rachet; eauto.
  Qed.

  Lemma sorted_app_in_gt :
    forall l1 l2 e e',
      sorted (l1 ++ l2) ->
      In e l1 ->
      In e' l2 ->
      eIndex e' < eIndex e.
  Proof.
    intros; induction l1; simpl in *; intuition.
    subst. specialize (H2 e'). concludes. intuition.
  Qed.

  Lemma Prefix_In :
    forall A (l : list A) l' x,
      Prefix l l' ->
      In x l ->
      In x l'.
  Proof.
    induction l; intros; simpl in *; intuition;
    subst; break_match; intuition; subst; intuition.
  Qed.
  
  Ltac get_invariant i :=
    match goal with
      | H : refined_raft_intermediate_reachable _ |- _ =>
        copy_apply i H
    end.
  
  Theorem state_machine_safety_nw'_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      state_machine_safety_nw' net.
  Proof.
    unfold state_machine_safety_nw'.
    intros.
    unfold committed in *. break_exists; intuition.
    destruct (lt_eq_lt_dec (eTerm x0) t); intuition.
    - find_copy_apply_lem_hyp append_entries_leaderLogs_invariant.
      copy_eapply_prop_hyp append_entries_leaderLogs AppendEntries; eauto.
      break_exists; break_and.
      get_invariant leader_completeness_invariant.
      get_invariant leaderLogs_sorted_invariant.
      unfold leaderLogs_sorted in *.
      unfold leader_completeness in *. break_and.
      eapply_prop_hyp leader_completeness_directly_committed directly_committed; eauto.
      repeat conclude_using eauto.
      get_invariant leaderLogs_entries_match_invariant.
      unfold leaderLogs_entries_match_host in *.
      match goal with
        | _ : In _ (log (snd (nwState _ ?x))),
              H : In _ (leaderLogs _),
                  H' : context [ entries_match ] |- _ =>
          let H'' := fresh "H" in
          pose proof H as H'';
            eapply H' with (h := x) in H''
      end.
      match goal with
        | [ _ : In ?e ?l,
                _ : In ?e' ?l,
                    _ : In ?e' ?l',
                        H : entries_match _ _ |- _ ] =>    
          specialize(H e' e' e)
      end; repeat concludes.
      match goal with
        | _ : ?P <-> ?Q, _ : ?P |- _ =>
          assert Q by intuition
      end.
      intuition.
      + left.
        eapply gt_le_trans; eauto.
        eapply maxIndex_is_max; eauto.
      + break_exists. intuition. subst.
        match goal with
          | |- context [eIndex ?x > eIndex ?e ] =>
            destruct (Compare_dec.lt_eq_lt_dec (eIndex x) (eIndex e))
        end; intuition.
        * right. right. right.
          apply in_app_iff. right.
          eapply prefix_contiguous; eauto. admit.
          find_copy_eapply_lem_hyp entries_contiguous; eauto.
          eapply contiguous_app; eauto. eapply entries_sorted_nw_invariant; eauto.
        * cut (e = x5); [intros; subst; intuition|].
          eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices.
      + subst. right. right. right.
        apply in_app_iff. right.
        get_invariant leaderLogs_contiguous_invariant.
        unfold leaderLogs_contiguous in *. find_copy_apply_hyp_hyp.
        eapply prefix_contiguous with (i := 0); eauto;
        [admit|match goal with
           | _ : In (_, ?l) (leaderLogs _), H : contiguous_range_exact_lo ?l _ |- _ =>
             unfold contiguous_range_exact_lo in H; intuition
         end].
    - subst.
      find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
      find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
      break_exists. simpl in *. intuition.
      + subst.
        match goal with
          | _ : In (_, ?l) (leaderLogs _),
                _ : In (_, ?l') (leaderLogs _) |- _ =>
            assert (l = l') by (eapply one_leaderLog_per_term_log_invariant; eauto)
        end.
        subst.
        match goal with
          | _ : removeAfterIndex _ _ = ?l1 ++ ?l2 |- _ =>
            rename l1 into new_entries; rename l2 into old_entries
        end.
        match goal with
          | |- context [?l1 ++ ?l2] =>
            rename l1 into new_msg_entries; rename l2 into old_msg_entries
        end.
        assert (In e (new_entries ++ old_entries)) by (find_reverse_rewrite; eauto using removeAfterIndex_le_In).
        do_in_app. intuition.
        * destruct (lt_eq_lt_dec prevLogIndex (eIndex e)); intuition;
          try solve [subst; find_apply_hyp_hyp; intuition].
          destruct (le_gt_dec (eIndex e) (maxIndex (new_msg_entries ++ old_msg_entries))); intuition.
          right. right. right.
          match goal with
            | |- In _ ?l => assert (contiguous_range_exact_lo l prevLogIndex) by
                  eauto using entries_contiguous
          end.
          unfold contiguous_range_exact_lo in *.
          intuition.
          match goal with
            | H : forall _, _ < _ <= _ -> exists _, _ |- _ =>
              specialize (H (eIndex e)); intuition
          end.
          break_exists. intuition.
          match goal with
            | _ : eIndex ?x = eIndex e |- _ =>
              rename x into e'
          end.
          cut (eTerm e' = eTerm e);
            eauto using network_host_entries.
          do_in_app. intuition; [repeat find_apply_hyp_hyp;
                                  repeat find_rewrite; auto|].
          exfalso.
          cut (eIndex e' < eIndex e); [intros; omega|].
          match goal with
            | _ : In e ?ll1, _ : In e' ?ll2, _ : Prefix ?ll2 ?ll2' |- _ =>
              apply sorted_app_in_gt with (l1 := ll1) (l2 := ll2') (e := e) (e' := e')
          end; eauto using Prefix_In.
          repeat find_reverse_rewrite.
          eauto using lift_logs_sorted, removeAfterIndex_sorted.
        * left.
          find_apply_lem_hyp maxIndex_is_max; [omega|].
          find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
      + break_exists. intuition. subst.
        match goal with
          | _ : In (_, ?l) (leaderLogs _),
                _ : In (_, ?l') (leaderLogs _) |- _ =>
            assert (l = l') by (eapply one_leaderLog_per_term_log_invariant; eauto)
        end.
        subst.
        match goal with
          | _ : removeAfterIndex _ _ = ?l1 ++ ?l2 |- _ =>
            rename l1 into new_entries; rename l2 into old_entries
        end.
        match goal with
          | |- context [?l1 ++ ?l2] =>
            rename l1 into new_msg_entries; rename l2 into old_msg_entries
        end.
        assert (In e (new_entries ++ old_entries)) by (find_reverse_rewrite; eauto using removeAfterIndex_le_In).
        match goal with
          | _ : In ?x old_entries |- _ => rename x into base_entry
        end.
        do_in_app. intuition.
        * assert (eIndex base_entry < eIndex e)
            by (eapply sorted_app_in_gt; eauto;
                find_reverse_rewrite; eauto using removeAfterIndex_sorted, lift_logs_sorted).
          destruct (le_gt_dec (eIndex e) (maxIndex (new_msg_entries ++ old_msg_entries))); intuition.
          right. right. right.
          match goal with
            | |- In _ ?l => assert (contiguous_range_exact_lo l (eIndex base_entry)) by
                  eauto using entries_contiguous
          end.
          unfold contiguous_range_exact_lo in *.
          intuition.
          match goal with
            | H : forall _, _ < _ <= _ -> exists _, _ |- _ =>
              specialize (H (eIndex e)); intuition
          end.
          break_exists. intuition.
          match goal with
            | _ : eIndex ?x = eIndex e |- _ =>
              rename x into e'
          end.
          cut (eTerm e' = eTerm e);
            eauto using network_host_entries.
          do_in_app. intuition; [repeat find_apply_hyp_hyp;
                                  repeat find_rewrite; auto|].
          exfalso.
          cut (eIndex e' < eIndex e); [intros; omega|].
          match goal with
            | _ : In e ?ll1, _ : In e' ?ll2, _ : Prefix ?ll2 ?ll2' |- _ =>
              apply sorted_app_in_gt with (l1 := ll1) (l2 := ll2') (e := e) (e' := e')
          end; eauto using Prefix_In.
          repeat find_reverse_rewrite.
          eauto using lift_logs_sorted, removeAfterIndex_sorted.
        * destruct (lt_eq_lt_dec (eIndex base_entry) (eIndex e)); intuition;
          [|cut (base_entry = e); intros; subst; intuition;
            eapply uniqueIndices_elim_eq; eauto;
            find_eapply_lem_hyp leaderLogs_sorted_invariant;
            eauto using sorted_uniqueIndices].
          right. right. right. apply in_app_iff; right.
          get_invariant leaderLogs_contiguous_invariant.
          unfold leaderLogs_contiguous in *. find_copy_apply_hyp_hyp.
          get_invariant leaderLogs_sorted_invariant.
          unfold leaderLogs_sorted in *. find_copy_apply_hyp_hyp.
          eapply prefix_contiguous with (i := (eIndex base_entry)); eauto; [admit|].
          find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
          eauto using contiguous_app, entries_contiguous.
      + subst.
        match goal with
          | _ : In (_, ?l) (leaderLogs _),
                _ : In (_, ?l') (leaderLogs _) |- _ =>
            assert (l = l') by (eapply one_leaderLog_per_term_log_invariant; eauto)
        end.
        subst.
        match goal with
          | _ : removeAfterIndex _ _ = ?l1 ++ ?l2 |- _ =>
            rename l1 into new_entries; rename l2 into old_entries
        end.
        match goal with
          | |- context [?l1 ++ ?l2] =>
            rename l1 into new_msg_entries; rename l2 into old_msg_entries
        end.
        assert (In e (new_entries ++ old_msg_entries)) by (find_reverse_rewrite; eauto using removeAfterIndex_le_In).
        assert (eIndex e > 0) by
            (repeat find_reverse_rewrite;
             find_apply_lem_hyp removeAfterIndex_in;
             get_invariant lift_log_matching;
             unfold log_matching, log_matching_hosts in *; intuition;
             unfold deghost in *; simpl in *; break_match; simpl in *;
               match goal with
                 | H : forall _ _, In _ _ -> _ |- _ => eapply H
               end; eauto).
        assert (0 < eIndex e) by omega.
        do_in_app. intuition.
        destruct (le_gt_dec (eIndex e) (maxIndex (new_msg_entries ++ old_msg_entries))); intuition.
        right. right. right.
        match goal with
          | |- In _ ?l => assert (contiguous_range_exact_lo l 0) by
                eauto using entries_contiguous
        end.
        unfold contiguous_range_exact_lo in *.
        intuition.
        match goal with
          | H : forall _, _ < _ <= _ -> exists _, _ |- _ =>
            specialize (H (eIndex e)); intuition
        end.
        break_exists. intuition.
        match goal with
          | _ : eIndex ?x = eIndex e |- _ =>
            rename x into e'
        end.
        cut (eTerm e' = eTerm e);
          eauto using network_host_entries.
        do_in_app. intuition; [repeat find_apply_hyp_hyp;
                                repeat find_rewrite; auto|].
        exfalso.
        cut (eIndex e' < eIndex e); [intros; omega|].
        match goal with
          | _ : In e ?ll1, _ : In e' ?ll2, _ : Prefix ?ll2 ?ll2' |- _ =>
            apply sorted_app_in_gt with (l1 := ll1) (l2 := ll2') (e := e) (e' := e')
        end; eauto using Prefix_In.
        repeat find_reverse_rewrite.
        eauto using lift_logs_sorted, removeAfterIndex_sorted.
  Admitted.

  Instance sms'i : state_machine_safety'interface.
  Proof.
    split.
    intuition.
    split.
    - auto using state_machine_safety_host'_invariant.
    - auto using state_machine_safety_nw'_invariant.
  Qed.
End StateMachineSafety'.
