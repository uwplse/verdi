Require Import GhostSimulations.
Require Import InverseTraceRelations.

Require Import Raft.
Require Import CommonTheorems.
Require Import TraceUtil.

Require Import SpecLemmas.

Require Import InputBeforeOutputInterface.
Require Import AppliedImpliesInputInterface.
Require Import OutputImpliesAppliedInterface.
Require Import LastAppliedCommitIndexMatchingInterface.
Require Import SortedInterface.
Require Import LogMatchingInterface.
Require Import StateMachineSafetyInterface.
Require Import MaxIndexSanityInterface.
Require Import UniqueIndicesInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Section InputBeforeOutput.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.
  Context {aiii : applied_implies_input_interface}.
  Context {si : sorted_interface}.
  Context {lacimi : lastApplied_commitIndex_match_interface}.
  Context {lmi : log_matching_interface}.
  Context {smsi : state_machine_safety_interface}.
  Context {misi : max_index_sanity_interface}.
  Context {uii : unique_indices_interface}.

  Section inner.
  Variables client id : nat.

  Fixpoint client_id_in l :=
    match l with
      | [] => false
      | e :: l' =>
        if (andb (eClient e =? client)
                 (eId e =? id)) then
          true
        else
          client_id_in l'
    end.

  Lemma client_id_in_true_in_applied_entries :
    forall net,
      client_id_in (applied_entries (nwState net)) = true ->
      in_applied_entries client id net.
  Proof.
    intros. unfold in_applied_entries.
    induction (applied_entries (nwState net)); simpl in *; try congruence.
    break_if; do_bool; intuition; do_bool; eauto;
    break_exists_exists; intuition.
  Qed.

  Lemma client_id_in_false_not_in_applied_entries :
    forall net,
      client_id_in (applied_entries (nwState net)) = false ->
      ~ in_applied_entries client id net.
  Proof.
    intros. unfold in_applied_entries.
    induction (applied_entries (nwState net)); simpl in *; try congruence; intuition.
    - break_exists; intuition.
    - break_if; try congruence.
      do_bool.
      break_exists; intuition; do_bool; subst; eauto.
  Qed.

  Lemma doGenericServer_applied_entries :
    forall ps h sigma os st' ms,
      raft_intermediate_reachable (mkNetwork ps sigma) ->
      doGenericServer h (sigma h) = (os, st', ms) ->
      exists es, applied_entries (update name_eq_dec sigma h st') = (applied_entries sigma) ++ es /\
            (forall e, In e es -> exists h, In e (log (sigma h)) /\ eIndex e <= commitIndex (sigma h)).
  Proof.
    intros.
    unfold doGenericServer in *. break_let. find_inversion.
    find_copy_apply_lem_hyp logs_sorted_invariant. unfold logs_sorted, logs_sorted_host in *.
    intuition.
    use_applyEntries_spec. subst. simpl in *. unfold raft_data in *.
    simpl in *.
    break_if; [|rewrite applied_entries_safe_update; simpl in *; eauto;
                exists nil; simpl in *; intuition].
    do_bool.
    match goal with
      | |- context [update _ ?sigma ?h ?st] => pose proof applied_entries_update sigma h st
    end.
    simpl in *. concludes. intuition; [find_rewrite; exists nil; simpl in *; intuition|].
    pose proof applied_entries_cases sigma.
    intuition; repeat find_rewrite; eauto;
    [eexists; intuition; eauto;
     find_apply_lem_hyp in_rev;
     find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto;
     find_apply_lem_hyp removeAfterIndex_in; eexists; intuition; eauto|].
    match goal with | H : exists _, _ |- _ => destruct H as [h'] end.
    repeat find_rewrite.
    find_apply_lem_hyp argmax_elim. intuition.
    match goal with
      | H : forall _: name, _ |- _ =>
        specialize (H h'); conclude H ltac:(eauto using all_fin_all)
    end.
    rewrite_update. simpl in *.
    update_destruct; subst; rewrite_update; simpl in *.
    + match goal with
        | h : name |- _ =>
          pose proof removeAfterIndex_partition (removeAfterIndex (log (sigma h)) (commitIndex (sigma h))) (lastApplied (sigma h))
      end.
      find_apply_lem_hyp rev_exists.
      break_exists_exists.
      repeat find_rewrite.
      rewrite <- removeAfterIndex_le by omega. intuition.
      find_eapply_lem_hyp app_in_2; eauto.
      find_apply_lem_hyp In_rev.
      find_copy_apply_lem_hyp removeAfterIndex_in.
      find_apply_lem_hyp removeAfterIndex_In_le; eauto.
    + match goal with
        | _ : ?h <> ?h' |- context [ removeAfterIndex ?l (commitIndex (?sigma ?h)) ] =>
          pose proof removeAfterIndex_partition (removeAfterIndex l (commitIndex (sigma h)))
               (lastApplied (sigma h'))
      end.
      find_apply_lem_hyp rev_exists.
      break_exists_exists.
      repeat match goal with | H : applied_entries _ = _ |- _ => clear H end.
      find_rewrite.
      erewrite <- removeAfterIndex_le; eauto.
      intuition.
      * f_equal. f_equal.
        find_copy_apply_lem_hyp lastApplied_commitIndex_match_invariant.
        eapply removeAfterIndex_same_sufficient; eauto;
        intros;
        eapply_prop_hyp lastApplied_commitIndex_match le; intuition eauto.
      * find_eapply_lem_hyp app_in_2; eauto.
        find_apply_lem_hyp In_rev.
        find_copy_apply_lem_hyp removeAfterIndex_in.
        find_apply_lem_hyp removeAfterIndex_In_le; eauto.
  Qed.

  
  Lemma findAtIndex_max_thing :
    forall net h e i,
      raft_intermediate_reachable net ->
      In e (log (nwState net h)) ->
      eIndex e > i ->
      1 <= i ->
      exists e',
        findAtIndex (log (nwState net h)) i = Some e'.
  Proof.
    intros.
    find_copy_apply_lem_hyp logs_sorted_invariant.
    pose proof log_matching_invariant.
    eapply_prop_hyp raft_intermediate_reachable raft_intermediate_reachable.
    unfold log_matching, log_matching_hosts, logs_sorted in *.
    intuition.
    match goal with
      | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
        specialize (H h i);
          conclude H ltac:(intuition; find_apply_lem_hyp maxIndex_is_max; eauto; omega)
    end.
    break_exists_exists. intuition. apply findAtIndex_intro; eauto using sorted_uniqueIndices.
  Qed.
  
  Lemma entries_max_thing :
    forall net p es,
      raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      mEntries (pBody p) = Some es ->
      es <> nil ->
      1 <= maxIndex es.
  Proof.
    intros.
    find_apply_lem_hyp maxIndex_non_empty.
    break_exists; intuition; find_rewrite.
    find_apply_lem_hyp log_matching_invariant.
    unfold log_matching, log_matching_nw in *.
    intuition. destruct (pBody p) eqn:?; simpl in *; try congruence.
    find_apply_hyp_hyp. intuition. find_inversion.
    find_apply_hyp_hyp. omega.
  Qed.

  Lemma logs_contiguous :
    forall net h,
      raft_intermediate_reachable net ->
      contiguous_range_exact_lo (log (nwState net h)) 0.
  Proof.
    intros.
    find_apply_lem_hyp log_matching_invariant.
    unfold log_matching, log_matching_hosts in *.
    intuition.
    unfold contiguous_range_exact_lo.
    intuition eauto.
    find_apply_hyp_hyp. intuition.
  Qed.

  Lemma entries_gt_0 :
    forall net p es e,
      raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      mEntries (pBody p) = Some es ->
      In e es ->
      0 < eIndex e.
  Proof.
    intros.
    find_apply_lem_hyp log_matching_invariant.
    unfold log_matching, log_matching_nw in *.
    intuition. destruct (pBody p) eqn:?; simpl in *; try congruence.
    find_inversion.
    find_apply_hyp_hyp. intuition.
    find_apply_hyp_hyp. omega.
  Qed.

  Lemma entries_gt_pli :
    forall net p e t n pli plt es ci,
      raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e es ->
      pli < eIndex e.
  Proof.
    intros.
    find_apply_lem_hyp log_matching_invariant.
    unfold log_matching, log_matching_nw in *.
    intuition. destruct (pBody p) eqn:?; simpl in *; try congruence.
    find_inversion.
    find_apply_hyp_hyp. intuition.
  Qed.
  
  Lemma sorted_app :
    forall l l',
      sorted (l ++ l') ->
      sorted l.
  Proof.
    induction l; simpl in *; intros; intuition eauto.
    - apply H0. intuition.
    - apply H0. intuition.
  Qed.
  
  Lemma handleMessage_applied_entries :
    forall net h h' m st' ms,
      raft_intermediate_reachable net ->
      In {| pBody := m; pDst := h; pSrc := h' |} (nwPackets net) ->
      handleMessage h' h m (nwState net h) = (st', ms) ->
      applied_entries (nwState net) = applied_entries (update name_eq_dec (nwState net) h st').
  Proof.
    intros. symmetry.
    unfold handleMessage in *. break_match; repeat break_let; repeat find_inversion.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleRequestVote_same_log, handleRequestVote_same_lastApplied.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleRequestVoteReply_same_log, handleRequestVoteReply_same_lastApplied.
    - find_copy_eapply_lem_hyp handleAppendEntries_logs_sorted;
      eauto using logs_sorted_invariant.
      apply applied_entries_safe_update; eauto using handleAppendEntries_same_lastApplied.
      find_apply_lem_hyp handleAppendEntries_log_detailed. intuition.
      + repeat find_rewrite. auto.
      + subst.
        find_copy_apply_lem_hyp state_machine_safety_invariant.
        unfold state_machine_safety in *. intuition.
        find_copy_apply_lem_hyp max_index_sanity_invariant. intuition.
        find_copy_apply_lem_hyp logs_sorted_invariant.
        unfold logs_sorted, maxIndex_sanity in *. intuition.
        apply removeAfterIndex_same_sufficient; eauto.
        * intros.
          copy_eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *.
            simpl in *; repeat (forwards; eauto; concludes).
            intuition; try omega;
            exfalso;
            find_eapply_lem_hyp findAtIndex_max_thing; eauto; try break_exists; try congruence;
            eauto using entries_max_thing;
            find_apply_lem_hyp logs_contiguous; auto; omega.
        * intros.
          find_copy_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_hosts in *. intuition.
          match goal with
            | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (eIndex e));
                forward H
          end;
            copy_eapply_prop_hyp log_matching_nw AppendEntries; eauto;
            repeat (forwards; [intuition eauto; omega|]; concludes);
            intuition; [eapply le_trans; eauto|].
          match goal with
            | H : exists _, _ |- _ => destruct H as [e']
          end.
          intuition.
          copy_eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *;
            simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
          match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
          intuition; try omega;
          [|find_copy_apply_lem_hyp UniqueIndices_invariant;
             unfold UniqueIndices in *; intuition;
             eapply rachet; [symmetry|idtac|idtac|idtac|idtac]; eauto].
          exfalso.
          find_eapply_lem_hyp findAtIndex_max_thing; eauto; try break_exists; try congruence;
          eauto using entries_max_thing.
      + repeat find_rewrite.
        find_copy_apply_lem_hyp state_machine_safety_invariant.
        find_copy_apply_lem_hyp max_index_sanity_invariant.
        unfold state_machine_safety, maxIndex_sanity in *. intuition.
        find_copy_apply_lem_hyp logs_sorted_invariant.
        unfold logs_sorted in *. intuition.
        eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
        * intros. eapply entries_gt_0; intuition eauto.
        * intros.
          copy_eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *;
            simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
          match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
          intuition; try omega; try solve [find_apply_lem_hyp logs_contiguous; auto; omega].
          exfalso.
          subst.
          break_exists. intuition.
          find_false.
          find_apply_lem_hyp maxIndex_non_empty.
          break_exists. intuition. repeat find_rewrite.
          f_equal.
          find_apply_lem_hyp findAtIndex_elim. intuition.
          eapply uniqueIndices_elim_eq with (xs := log st'); eauto using sorted_uniqueIndices.
          unfold state_machine_safety_nw in *.
          eapply_prop_hyp commit_recorded In; intuition; eauto; try omega;
          try solve [find_apply_lem_hyp logs_contiguous; auto; omega].
          unfold commit_recorded. intuition.
      + repeat find_rewrite.
        find_copy_apply_lem_hyp logs_sorted_invariant.
        unfold logs_sorted in *. intuition.
        eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
        * { intros. do_in_app. intuition.
            - eapply entries_gt_0; eauto. reflexivity.
            - find_apply_lem_hyp removeAfterIndex_in.
              find_apply_lem_hyp logs_contiguous; eauto.
          }
        * find_apply_lem_hyp max_index_sanity_invariant.
          unfold maxIndex_sanity in *. intuition.
        * intros.
          find_copy_apply_lem_hyp state_machine_safety_invariant.
          unfold state_machine_safety in *. break_and.
          copy_eapply_prop_hyp state_machine_safety_nw In; eauto.
          simpl in *. intuition eauto. forwards; eauto. concludes.
          forwards; [unfold commit_recorded in *; intuition eauto|].
          concludes.
          intuition; apply in_app_iff;
          try solve [right; eapply removeAfterIndex_le_In; eauto; omega];
          exfalso.
          find_eapply_lem_hyp findAtIndex_max_thing; eauto using entries_max_thing.
          break_exists; congruence.
      + break_exists. intuition. subst.
        repeat find_rewrite.
        find_copy_apply_lem_hyp logs_sorted_invariant.
        unfold logs_sorted in *. intuition.
        eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
        * { intros. do_in_app. intuition.
            - eapply entries_gt_0; eauto. reflexivity.
            - find_apply_lem_hyp removeAfterIndex_in.
              find_apply_lem_hyp logs_contiguous; eauto.
          }
        * find_apply_lem_hyp max_index_sanity_invariant.
          unfold maxIndex_sanity in *. intuition.
        * {
            intros.
            find_copy_apply_lem_hyp state_machine_safety_invariant.
            unfold state_machine_safety in *. break_and.
            copy_eapply_prop_hyp state_machine_safety_nw In; eauto.
            simpl in *. intuition eauto. forwards; eauto. concludes.
            forwards; [unfold commit_recorded in *; intuition eauto|].
            concludes.
            intuition; apply in_app_iff;
            try solve [right; eapply removeAfterIndex_le_In; eauto; omega].
            subst.
            find_apply_lem_hyp maxIndex_non_empty.
            break_exists. intuition. repeat find_rewrite.
            find_apply_lem_hyp findAtIndex_elim. intuition.
            find_false. f_equal.
            eapply uniqueIndices_elim_eq with (xs := log (nwState net h));
              eauto using sorted_uniqueIndices.
            unfold state_machine_safety_nw in *.
            eapply rachet; eauto using sorted_app, sorted_uniqueIndices.
            copy_eapply_prop_hyp commit_recorded In; intuition; eauto; try omega;
            unfold commit_recorded; intuition.
            - exfalso.
              pose proof entries_gt_pli.
              eapply_prop_hyp AppendEntries AppendEntries;
                [|idtac|simpl; eauto|]; eauto. omega.
            -  exfalso.
              pose proof entries_gt_pli.
              eapply_prop_hyp AppendEntries AppendEntries;
                [|idtac|simpl; eauto|]; eauto. omega.
          }
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleAppendEntriesReply_same_log, handleAppendEntriesReply_same_lastApplied.
  Qed.

  Lemma handleMessage_log :
    forall net h h' h'' e m st' ms,
      raft_intermediate_reachable net ->
      In {| pBody := m; pDst := h; pSrc := h' |} (nwPackets net) ->
      handleMessage h' h m (nwState net h) = (st', ms) ->
      In e (log (update name_eq_dec (nwState net) h st' h'')) ->
      applied_implies_input_state (eClient e) (eId e) (eInput e) net.
  Proof.
    intros.
    unfold handleMessage in *. break_match; repeat break_let; repeat find_inversion.
    - find_apply_lem_hyp handleRequestVote_same_log.
      update_destruct; subst; rewrite_update; repeat find_rewrite;
      unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
    - update_destruct; subst; rewrite_update; repeat find_rewrite;
      try find_rewrite_lem handleRequestVoteReply_same_log;
      unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
    - update_destruct; subst; rewrite_update; repeat find_rewrite;
      try solve [unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto].
      find_apply_lem_hyp handleAppendEntries_log. intuition.
      + repeat find_rewrite. unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
      + subst.
        unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
        right. repeat eexists; eauto. reflexivity.
      + repeat find_rewrite. do_in_app. intuition.
        * unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
          right. repeat eexists; eauto. reflexivity.
        * find_apply_lem_hyp removeAfterIndex_in.
          unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
    - find_apply_lem_hyp handleAppendEntriesReply_log.
      update_destruct; subst; rewrite_update; repeat find_rewrite;
      unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
  Qed.
  
  Lemma handleInput_applied_entries :
    forall net h inp os st' ms,
      raft_intermediate_reachable net ->
      handleInput h inp (nwState net h) = (os, st', ms) ->
      applied_entries (nwState net) = applied_entries (update name_eq_dec (nwState net) h st').
  Proof.
    intros. symmetry.
    unfold handleInput in *. break_match; repeat break_let; repeat find_inversion.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleTimeout_log_same, handleTimeout_lastApplied.
    - apply applied_entries_safe_update; eauto using handleClientRequest_lastApplied.

      destruct (log st') using (handleClientRequest_log_ind ltac:(eauto)); auto.

      simpl in *. break_if; auto.
      exfalso.
      do_bool.
      find_apply_lem_hyp max_index_sanity_invariant.
      unfold maxIndex_sanity, maxIndex_lastApplied in *.
      intuition.
      match goal with
        | H : forall _, _ |- _ => specialize (H h)
      end. omega.
  Qed.

  Lemma handleInput_log :
    forall net h inp os st' ms h' e,
      raft_intermediate_reachable net ->
      handleInput h inp (nwState net h) = (os, st', ms) ->
      In e (log (update name_eq_dec (nwState net) h st' h')) ->
      (applied_implies_input_state (eClient e) (eId e) (eInput e) net \/
       inp = ClientRequest (eClient e) (eId e) (eInput e)).
  Proof.
    intros.
    unfold handleInput in *. break_match; repeat break_let; repeat find_inversion.
    - left.
      find_apply_lem_hyp handleTimeout_log_same.
      update_destruct; subst; rewrite_update; repeat find_rewrite;
      unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
    - find_apply_lem_hyp handleClientRequest_log. intuition.
      + left.
        update_destruct; subst; rewrite_update; repeat find_rewrite;
        unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
      + break_exists. intuition.
        update_destruct; subst; rewrite_update; repeat find_rewrite;
        try solve [left; unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto].
        simpl in *. intuition; subst; intuition.
        left; unfold applied_implies_input_state, correct_entry; eexists; intuition; eauto.
  Qed.
  
  Lemma in_applied_entries_step_applied_implies_input_state' :
    forall (failed : list name) net failed' net' o,
      raft_intermediate_reachable net ->
      step_f (failed, net) (failed', net') o ->
      ~ in_applied_entries client id net ->
      in_applied_entries client id net' ->
      (exists e,
         eClient e = client /\
         eId e = id /\
         applied_implies_input_state client id (eInput e) net) \/
      exists h o' inp,
        o = (h, inl (ClientRequest client id inp)) :: o'.
  Proof.
    intros. match goal with H : step_f _ _ _ |- _ => invcs H end; intuition.
    - left. unfold RaftNetHandler in *. repeat break_let. subst.
      unfold in_applied_entries in *.
      break_exists_exists. intuition.
      find_inversion.
      match goal with
        | Hdgs : doGenericServer ?h ?st' = _,
          Hdl : doLeader ?st ?h = _, _ :context [update _ (nwState ?net) ?h ?st''] |- _ =>
          replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq;
            replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq;
            let H := fresh "H" in
            assert (update name_eq_dec (nwState net) h st'' =
                    update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') as H by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H in *; clear H
      end.
      find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
      find_eapply_lem_hyp RIR_doLeader; simpl in *; eauto.
      simpl in *.
      find_copy_apply_lem_hyp handleMessage_applied_entries; repeat find_rewrite; eauto;
      try solve [destruct p; simpl in *; intuition].
      find_copy_apply_lem_hyp doLeader_appliedEntries.
      find_eapply_lem_hyp doGenericServer_applied_entries; eauto.
      break_exists. intuition.
      unfold ghost_data in *. simpl in *.
      repeat find_rewrite.
      do_in_app. intuition.
      + find_false. eexists; intuition; repeat find_rewrite; eauto.
      + find_apply_hyp_hyp. break_exists. intuition.
        eapply handleMessage_log with (h'' := x1); eauto;
        [destruct p; simpl in *; repeat find_rewrite; intuition|].
        update_destruct; subst; rewrite_update; eauto.
        find_apply_lem_hyp doLeader_log. repeat find_rewrite. auto.
    - unfold RaftInputHandler in *. repeat break_let. subst.
      unfold in_applied_entries in *.
      break_exists_exists. intuition.
      find_inversion.
      match goal with
        | Hdgs : doGenericServer ?h ?st' = _,
          Hdl : doLeader ?st ?h = _, _ :context [update _ (nwState ?net) ?h ?st''] |- _ =>
          replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq;
            replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq;
            let H := fresh "H" in
            assert (update name_eq_dec (nwState net) h st'' =
                    update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') as H by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H in *; clear H
      end.
      find_copy_eapply_lem_hyp RIR_handleInput; eauto.
      find_eapply_lem_hyp RIR_doLeader; simpl in *; eauto.
      simpl in *.
      find_copy_apply_lem_hyp handleInput_applied_entries; repeat find_rewrite; eauto;
      try solve [destruct p; simpl in *; intuition].
      find_copy_apply_lem_hyp doLeader_appliedEntries.
      find_eapply_lem_hyp doGenericServer_applied_entries; eauto.
      break_exists. intuition.
      unfold ghost_data in *. simpl in *.
      repeat find_rewrite.
      match goal with
        | H : In _ _ -> False |- _ => clear H
      end.
      do_in_app. intuition.
      + find_false. eexists; intuition; repeat find_rewrite; eauto.
      + find_apply_hyp_hyp. break_exists. intuition.
        find_apply_lem_hyp doLeader_log.
        match goal with
          | H : _ |- _ =>
            eapply handleInput_log with (h' := x1) in H
        end; eauto;
        [|update_destruct; subst; eauto; rewrite_update; repeat find_rewrite; eauto].
        intuition; subst;
        repeat find_rewrite; eauto.
    - find_false.
      unfold in_applied_entries in *.
      break_exists_exists. intuition.
      match goal with
        | H : In _ (applied_entries _) |- In _ (applied_entries ?sig) =>
          erewrite applied_entries_log_lastApplied_same with (sigma := sig) in H
      end; auto;
      intros; simpl in *; break_if; auto.
  Qed.
  
  Lemma in_applied_entries_step_applied_implies_input_state :
    forall (s : list name * network) s' tr o,
      refl_trans_1n_trace step_f step_f_init s tr ->
      ~ in_applied_entries client id (snd s) ->
      step_f s s' o ->
      in_applied_entries client id (snd s') ->
      (exists e,
        eClient e = client /\
        eId e = id /\
        applied_implies_input_state client id (eInput e) (snd s)) \/
      exists h o' inp,
        o = (h, inl (ClientRequest client id inp)) :: o'.
  Proof.
    intros.
    destruct s as (failed, net).
    destruct s' as (failed', net'). simpl in *.
    find_apply_lem_hyp step_f_star_raft_intermediate_reachable.
    eauto using in_applied_entries_step_applied_implies_input_state'.
  Qed.

  Lemma in_input_not_in_output_input_before_output :
    forall client id i tr,
      in_input_trace client id i tr ->
      ~ key_in_output_trace client id tr ->
      input_before_output client id tr.
  Proof.
    intros. induction tr; simpl in *; intuition.
    - unfold in_input_trace in *. break_exists; simpl in *; intuition.
    - unfold in_input_trace in *.
      break_exists. simpl in *. intuition.
      + subst. unfold input_before_output. simpl.
        left. do_bool; intuition; do_bool; auto.
      + unfold input_before_output. simpl. right. intuition.
        * unfold key_in_output_trace in *. 
          apply Bool.not_true_iff_false. intuition.
          find_false. unfold is_output_with_key in *.
          break_match; subst. repeat break_match; try congruence.
          exists l, n. intuition.
        * conclude_using eauto.
          conclude_using
            ltac:(intros; find_false; unfold key_in_output_trace in *;
                    break_exists_exists; intuition).
          eauto.
  Qed.

  Lemma input_before_output_not_key_in_output_trace_snoc_key :
    forall client id tr h inp tr',
      ~ key_in_output_trace client id tr ->
      input_before_output client id
                          (tr ++ (h, inl (ClientRequest client id inp)) :: tr').
  Proof.
    intros. induction tr; simpl in *.
    -unfold input_before_output. simpl in *.
     left. repeat (do_bool; intuition).
    - unfold input_before_output. simpl. right. intuition.
      + unfold key_in_output_trace in *.
        apply Bool.not_true_iff_false. intuition.
        find_false. unfold is_output_with_key in *.
        break_match; subst. repeat break_match; try congruence.
        exists l, n. intuition.
      + conclude_using
          ltac:(intros; find_false; unfold key_in_output_trace in *;
                  break_exists_exists; intuition).
        eauto.
  Qed.

  Instance TR : InverseTraceRelation step_f :=
    {
      init := step_f_init;
      T := input_before_output client id;
      R := fun s => in_applied_entries client id (snd s) 
    }.
  Proof.
    - intros.
      destruct (client_id_in (applied_entries (nwState (snd s)))) eqn:?;
      eauto using client_id_in_true_in_applied_entries, client_id_in_false_not_in_applied_entries.
    - intros.
      unfold input_before_output in *.
      eauto using before_func_app.
    - intuition. simpl in *.
      unfold in_applied_entries, applied_entries in *. simpl in *.
      break_match; simpl in *; break_exists; intuition.
    - intros.
      destruct s as (failed, net).
      destruct s' as (failed', net'). simpl in *.
      find_eapply_lem_hyp in_applied_entries_step_applied_implies_input_state; eauto.
      break_or_hyp.
      + break_exists. intuition.
        find_eapply_lem_hyp applied_implies_input; eauto.
        apply before_func_app.
        destruct (key_in_output_trace_dec client id tr);
          [find_eapply_lem_hyp output_implies_applied; eauto; intuition|].
        fold (input_before_output client id tr).
        subst. eauto using in_input_not_in_output_input_before_output.
      + destruct (key_in_output_trace_dec client id tr);
        [find_eapply_lem_hyp output_implies_applied; eauto; intuition|].
        break_exists. subst.
        eauto using input_before_output_not_key_in_output_trace_snoc_key.
  Defined.

  Theorem output_implies_input_before_output :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      key_in_output_trace client id tr ->
      input_before_output client id tr.
  Proof.
    intros. pose proof (inverse_trace_relations_work (failed, net) tr).
    concludes.
    find_eapply_lem_hyp output_implies_applied; eauto.
    intuition.
  Qed.

  End inner.

  Instance iboi : input_before_output_interface.
  Proof.
    split.
    intros.
    eapply output_implies_input_before_output; eauto.
  Qed.
End InputBeforeOutput.
