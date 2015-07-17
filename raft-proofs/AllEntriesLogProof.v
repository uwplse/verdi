Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import LogsLeaderLogsInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import RefinedLogMatchingLemmasInterface.
Require Import AllEntriesLeaderLogsTermInterface.
Require Import LeaderLogsContiguousInterface.
Require Import OneLeaderLogPerTermInterface.
Require Import LeaderLogsSortedInterface.
Require Import TermSanityInterface.
Require Import AllEntriesTermSanityInterface.

Require Import AllEntriesLogInterface.

Section AllEntriesLog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {llli : logs_leaderLogs_interface}.
  Context {aerlli : append_entries_leaderLogs_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {aellti : allEntries_leaderLogs_term_interface}.
  Context {llci : leaderLogs_contiguous_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {llsi : leaderLogs_sorted_interface}.
  Context {tsi : term_sanity_interface}.
  Context {rri : raft_refinement_interface}.
  Context {aetsi : allEntries_term_sanity_interface}.
  

  (* strategy : prove allEntries_log as inductive invariant, then
     prove allEntries_leaderLogs inductive from that *)


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

  Definition no_entries_past_current_term_host_lifted net :=
    forall (h : name) e,
      In e (log (snd (nwState net h))) ->
      eTerm e <= currentTerm (snd (nwState net h)).

  Lemma no_entries_past_current_term_host_lifted_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      no_entries_past_current_term_host_lifted net.
  Proof.
    unfold no_entries_past_current_term_host_lifted.
    pose proof deghost_spec.
    do 4 intro.
    repeat find_reverse_higher_order_rewrite.
    eapply lift_prop; eauto.
    intros.
    find_apply_lem_hyp no_entries_past_current_term_invariant; eauto.
  Qed.
  
(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.


  Lemma appendEntries_haveNewEntries_false :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      haveNewEntries (snd (nwState net h)) es = false ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof.
    intros.
    unfold haveNewEntries in *. do_bool. intuition;
      [unfold not_empty in *; break_match; subst; simpl in *; intuition; congruence|].
    break_match; try congruence.
    do_bool. find_apply_lem_hyp findAtIndex_elim. intuition.
    assert (es <> nil) by (destruct es; subst; simpl in *; intuition; congruence).
    find_eapply_lem_hyp maxIndex_non_empty.
    break_exists. intuition.
    find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
    match goal with
      | H : In e es |- _ => copy_eapply maxIndex_is_max H; eauto
    end.
    repeat find_rewrite.
    find_eapply_lem_hyp entries_match_nw_host_invariant; eauto.
  Qed.
  
  Lemma maxIndex_le :
    forall l1 l2,
      sorted l1 ->
      contiguous_range_exact_lo l1 0 ->
      findAtIndex l1 (maxIndex l2) = None ->
      l2 = nil
      \/ (exists e, In e l2 /\ eIndex e = 0)
      \/ maxIndex l1 <= maxIndex l2.
  Proof.
    intros. destruct l2; intuition.
    simpl in *. right.
    destruct l1; intuition.
    find_copy_eapply_lem_hyp findAtIndex_None; simpl in *; eauto.
    unfold contiguous_range_exact_lo in *.
    simpl in *. intuition.
    destruct (lt_eq_lt_dec 0 (eIndex e)); intuition; eauto.
    destruct (lt_eq_lt_dec (eIndex e0) (eIndex e)); intuition.
    exfalso. repeat break_if; do_bool; intuition.
    match goal with
      | H : forall _, _ < _ <= _ -> _ |- _ =>
        specialize (H (eIndex e))
    end; conclude_using omega.
    simpl in *. break_exists. intuition; subst; intuition.
    eapply findAtIndex_None; eauto.
  Qed.

  Lemma maxIndex_le' :
    forall l1 l2 i,
      sorted l1 ->
      contiguous_range_exact_lo l1 0 ->
      l2 <> nil ->
      contiguous_range_exact_lo l2 i ->
      findAtIndex l1 (maxIndex l2) = None ->
      maxIndex l1 <= maxIndex l2.
  Proof.
    intros. find_eapply_lem_hyp maxIndex_le; intuition; eauto.
    break_exists. intuition.
    unfold contiguous_range_exact_lo in *.
    intuition.
    find_insterU. conclude_using eauto. omega.
  Qed.
                                 
  Lemma sorted_app_in_in :
    forall l1 l2 e e',
      sorted (l1 ++ l2) ->
      In e l1 ->
      In e' l2 ->
      eIndex e' < eIndex e.
  Proof.
    induction l1; intros; simpl in *; intuition; eauto.
    subst. find_insterU. conclude_using ltac:(apply in_app_iff; intuition eauto).
    intuition.
  Qed.
  
  Lemma sorted_app_sorted_app_in1_in2 :
    forall l1 l2 l3 e e',
      sorted (l1 ++ l3) ->
      sorted (l2 ++ l3) ->
      In e l1 ->
      In e' (l2 ++ l3) ->
      eIndex e' = eIndex e ->
      In e' l2.
  Proof.
    intros. do_in_app. intuition.
    match goal with
      | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ =>
        eapply sorted_app_in_in in H
    end; eauto.  omega.
  Qed.

  Lemma sorted_app_sorted_app_in1_in2_prefix :
    forall l1 l2 l3 l4 e e',
      sorted (l1 ++ l3) ->
      sorted (l2 ++ l4) ->
      Prefix l4 l3 ->
      In e l1 ->
      In e' (l2 ++ l4) ->
      eIndex e' = eIndex e ->
      In e' l2.
  Proof.
    intros. do_in_app. intuition.
    find_eapply_lem_hyp Prefix_In; [|eauto].
    match goal with
      | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ =>
        eapply sorted_app_in_in in H
    end; eauto. omega.
  Qed.
  
  Lemma sorted_app_in2_in2 :
    forall l1 l2 e e',
      sorted (l1 ++ l2) ->
      In e' (l1 ++ l2) ->
      In e l2 ->
      eIndex e' = eIndex e ->
      In e' l2.
  Proof.
    intros. do_in_app. intuition.
    match goal with
      | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ =>
        eapply sorted_app_in_in in H
    end; eauto.  omega.
  Qed.

  
(*  Lemma sorted_app_in3_in4_prefix :
    forall l1 l2 l3 l4 e e',
      sorted (l1 ++ l3) ->
      sorted (l2 ++ l4) ->
      Prefix l4 l3 ->
      In e l3 ->
      In e' (l2 ++ l4) ->
      eIndex e' = eIndex e ->
      In e' l4.
  Proof.
    intros. do_in_app. intuition.
    match goal with
      | H : sorted (?l ++ ?l'), _ : In _ ?l, _ : In _ ?l' |- _ =>
        eapply sorted_app_in_in in H
    end; eauto.  omega.
  Qed.
  *)
  Lemma sorted_term_index_le :
    forall l e e',
      sorted l ->
      In e l ->
      In e' l ->
      eTerm e' < eTerm e ->
      eIndex e' <= eIndex e.
  Proof.
    induction l; intros; simpl in *; intuition; subst_max; intuition.
    - find_apply_hyp_hyp. intuition.
    - find_apply_hyp_hyp. intuition.
  Qed.
  Lemma term_ne_in_l2 :
    forall l e e' l1 l2,
      sorted l ->
      In e l ->
      (forall e', In e' l -> eTerm e' <= eTerm e) ->
      removeAfterIndex l (eIndex e) = l1 ++ l2 ->
      (forall e', In e' l1 -> eTerm e' = eTerm e) ->
      In e' l ->
      eTerm e' <> eTerm e ->
      In e' l2.
  Proof.
    intros.
    assert (eIndex e' <= eIndex e) by
        (eapply sorted_term_index_le; eauto;
         find_apply_hyp_hyp;
         destruct (lt_eq_lt_dec (eTerm e') (eTerm e)); intuition).
    find_eapply_lem_hyp removeAfterIndex_le_In; eauto.
    repeat find_rewrite.
    do_in_app. intuition.
    find_apply_hyp_hyp. intuition.
  Qed.

  Lemma Prefix_maxIndex_eq :
    forall l l',
      Prefix l l' ->
      l <> nil ->
      maxIndex l = maxIndex l'.
  Proof.
    intros.
    induction l; simpl in *; intuition.
    break_match; intuition. subst. simpl. auto.
  Qed.

  Lemma sorted_gt_maxIndex :
    forall e l1 l2,
      sorted (e :: l1 ++ l2) ->
      l2 <> nil ->
      maxIndex l2 < eIndex e.
  Proof.
    intros; induction l1; simpl in *; intuition.
    - destruct l2; simpl in *; intuition.
      match goal with
        | H : forall _, ?e = _ \/ _ -> _ |- _ =>
          specialize (H e)
      end; intuition.
  Qed.
  
  Lemma allEntries_log_append_entries :
    refined_raft_net_invariant_append_entries allEntries_log.
  Proof.
    red. unfold allEntries_log in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *;
    [|find_apply_hyp_hyp; intuition;
      right; break_exists_exists; intuition;
      repeat find_higher_order_rewrite;
      destruct_update; simpl in *;
      eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto].
    find_eapply_lem_hyp update_elections_data_appendEntries_allEntries_detailed; eauto.
    intuition;
      [|repeat find_rewrite;
         find_eapply_lem_hyp appendEntries_haveNewEntries_false; eauto].
    find_copy_apply_hyp_hyp. intuition;
      [|right; break_exists_exists; intuition;
        repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto;
        try rewrite update_elections_data_appendEntries_leaderLogs; eauto; subst;
        find_apply_lem_hyp handleAppendEntries_currentTerm_leaderId; intuition;
        repeat find_rewrite; auto].
    destruct (in_dec entry_eq_dec e (log d)); intuition.
    right.
    find_copy_apply_lem_hyp handleAppendEntries_log_detailed.
    intuition; repeat find_rewrite; intuition.
    - subst.
      find_copy_eapply_lem_hyp allEntries_term_sanity_invariant; eauto.
      destruct (lt_eq_lt_dec t0 (currentTerm d)); intuition; unfold ghost_data in *; simpl in *; try omega.
      + find_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
        break_exists. break_and.
        match goal with
          | H : In (?t, ?ll) (leaderLogs (fst (nwState _ ?leader))) |- _ =>
            (exists t, leader, ll)
        end.
        split;
          [repeat find_higher_order_rewrite;
            destruct_update; simpl in *;
            eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto|];
          split; auto; intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
          subst. repeat find_rewrite. intuition.
      + subst.
        find_eapply_lem_hyp allEntries_leaderLogs_term_invariant; eauto. intuition.
        * subst. exfalso.
          find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
          find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
          break_exists; intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
          subst. clean.
          repeat find_rewrite.
          find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
          conclude_using eauto. subst.
          match goal with
            | H : In _ _ -> False |- _ =>
              apply H
          end.
          find_copy_eapply_lem_hyp entries_sorted_invariant; eauto.
          unfold entries_sorted in *.
          repeat find_rewrite.
          match goal with
            | _ : removeAfterIndex ?l (eIndex ?e) = _ |- _ =>
              assert (In e (removeAfterIndex l (eIndex e))) by
                  (eapply removeAfterIndex_le_In; eauto)
          end.
          repeat find_rewrite.
          do_in_app; intuition.
          assert (exists e', eIndex e' = eIndex e /\ In e' (x1 ++ x4)) by
              (eapply entries_contiguous_nw_invariant; eauto;
               intuition; [eapply entries_contiguous_invariant; eauto|];
               eapply le_trans; [eapply maxIndex_is_max; eauto|];
               eapply maxIndex_le'; eauto;
               [eapply entries_contiguous_invariant; eauto|
                eapply entries_contiguous_nw_invariant; eauto]).
          break_exists. intuition.
          find_copy_eapply_lem_hyp sorted_app_sorted_app_in1_in2. Focus 5. eauto. Focus 4. eauto.
          all:(try solve [eapply entries_sorted_nw_invariant; eauto]).
          all:(try solve [repeat find_reverse_rewrite; eauto using removeAfterIndex_sorted]).
          find_apply_hyp_hyp.
          find_eapply_lem_hyp entries_match_nw_host_invariant; eauto; repeat conclude_using eauto.
          match goal with
            | H : eIndex _ = eIndex _ |- _ =>
              eapply uniqueIndices_elim_eq in H
          end; eauto using sorted_uniqueIndices.
          subst. auto.
        * exfalso.
          find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
          break_exists; intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
          subst. clean.
          find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
          conclude_using eauto. subst.
          match goal with
            | H : In _ _ -> False |- _ =>
              apply H
          end.
          repeat find_rewrite. apply in_app_iff; intuition.
    - subst.
      find_copy_eapply_lem_hyp allEntries_term_sanity_invariant; eauto.
      destruct (lt_eq_lt_dec t0 (currentTerm d)); intuition; unfold ghost_data in *; simpl in *; try omega.
      + find_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
        break_exists. break_and.
        match goal with
          | H : In (?t, ?ll) (leaderLogs (fst (nwState _ ?leader))) |- _ =>
            (exists t, leader, ll)
        end. find_higher_order_rewrite.
        split;
          [subst; find_higher_order_rewrite;
            destruct_update; simpl in *;
            eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto|];
          split; auto.
        intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
        subst. repeat find_rewrite. intuition.
      + subst.
        find_eapply_lem_hyp allEntries_leaderLogs_term_invariant; eauto. intuition.
        * { subst. exfalso.
            find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
            find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
            break_exists; intuition;
            [break_exists; intuition;
             find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
            subst. clean.
            repeat find_rewrite.
            find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
            conclude_using eauto. subst.
            match goal with
              | H : In _ _ -> False |- _ =>
                apply H
            end.
            find_copy_eapply_lem_hyp entries_sorted_invariant; eauto.
            unfold entries_sorted in *.
            repeat find_rewrite.
            match goal with
              | _ : removeAfterIndex ?l (eIndex ?e) = _ |- _ =>
                assert (In e (removeAfterIndex l (eIndex e))) by
                    (eapply removeAfterIndex_le_In; eauto)
            end.
            repeat find_rewrite.
            do_in_app; intuition.
            find_apply_lem_hyp findAtIndex_elim. intuition.
            find_copy_apply_lem_hyp maxIndex_non_empty.
            break_exists.
            intuition.
            match goal with
              | _ : In ?e' (log _), _ : maxIndex ?l = eIndex ?e' |- _ =>
                destruct (le_lt_dec (eIndex e) (maxIndex l))
            end.
            - assert (exists e', eIndex e' = eIndex e /\ In e' (x1 ++ x4)) by
                  (eapply entries_contiguous_nw_invariant; eauto; intuition;
                   eapply entries_gt_0_invariant; eauto).
              break_exists. intuition.
              find_copy_eapply_lem_hyp sorted_app_sorted_app_in1_in2. Focus 5. eauto. Focus 4. eauto.
              all:(try solve [eapply entries_sorted_nw_invariant; eauto]).
              all:(try solve [repeat find_reverse_rewrite; eauto using removeAfterIndex_sorted]).
              find_apply_hyp_hyp.
              find_eapply_lem_hyp entries_match_nw_host_invariant; eauto; repeat conclude_using eauto.
              match goal with
                | H : eIndex _ = eIndex _ |- _ =>
                  eapply uniqueIndices_elim_eq in H
              end; eauto using sorted_uniqueIndices.
              subst. auto.
            - exfalso.
              repeat find_rewrite.
              match goal with
                | _ : eIndex ?e' = eIndex ?x,
                  _ : eIndex ?x < ?i,
                  _ : context [removeAfterIndex ?l ?i] |- _ =>
                  assert (In e' (removeAfterIndex l i)) by
                      (eapply removeAfterIndex_le_In; auto; omega)
              end.
              repeat find_rewrite.
              do_in_app. intuition.
              + find_copy_eapply_lem_hyp sorted_app_sorted_app_in1_in2. Focus 4. eauto.
                all:eauto.
                all:(try solve [eapply entries_sorted_nw_invariant; eauto]).
                all:(try solve [repeat find_reverse_rewrite; eauto using removeAfterIndex_sorted]).
                repeat find_apply_hyp_hyp. repeat find_rewrite. intuition.
              + find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                find_copy_eapply_lem_hyp sorted_app_in2_in2. Focus 3. eauto.
                all:eauto.
                all:(try solve [eapply entries_sorted_nw_invariant; eauto]).
                match goal with
                  | H : eIndex ?e1 = eIndex ?e2, _ : In ?e1 ?ll, _ : In ?e2 ?ll |- _ =>
                    eapply uniqueIndices_elim_eq with (xs0 := ll) in H
                end; eauto using sorted_uniqueIndices.
                subst. intuition.
          }
        * exfalso.
          find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
          break_exists; intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
          subst. clean.
          find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
          conclude_using eauto. subst.
          match goal with
            | H : In _ _ -> False |- _ =>
              apply H
          end.
          repeat find_rewrite. apply in_app_iff; intuition.
    - find_copy_eapply_lem_hyp allEntries_term_sanity_invariant; eauto.
      destruct (lt_eq_lt_dec t0 t); intuition; unfold ghost_data in *; simpl in *; try omega.
      + match goal with
          | H : context [pBody] |- _ =>
            copy_eapply append_entries_leaderLogs_invariant H
        end; eauto.
        break_exists. break_and. subst.
        match goal with
          | H : In (?t, ?ll) (leaderLogs (fst (nwState _ ?leader))) |- _ =>
            (exists t, leader, ll)
        end.
        split;
          [find_higher_order_rewrite;
            destruct_update; simpl in *;
            eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto|];
          split; auto. intuition; subst.
        * find_false.
          apply in_app_iff. right. eapply removeAfterIndex_le_In; eauto.
          find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
          eapply le_trans; [eapply maxIndex_is_max; eauto|]. omega.
        * {
            break_exists. intuition. unfold Prefix_sane in *. intuition.
            - destruct (le_lt_dec (eIndex e) (eIndex x3)).
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. right. apply removeAfterIndex_le_In; auto.
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. left.
                apply in_app_iff. right.
                find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                eapply prefix_contiguous; eauto.
                find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
                eapply contiguous_app; eauto.
                eapply entries_contiguous_nw_invariant; eauto.
            - find_false.
              repeat find_rewrite.
              apply in_app_iff. right.
              find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
              apply removeAfterIndex_le_In; auto.
              eapply maxIndex_is_max; eauto.
          }
        * find_false. intuition.
      + subst.
        find_eapply_lem_hyp allEntries_leaderLogs_term_invariant; eauto. intuition.
        * { subst. exfalso.
            find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
            find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
            break_exists. break_and.
            repeat find_rewrite.
            find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto.
            conclude_using eauto. subst. intuition.
            - repeat find_rewrite.
              destruct (le_lt_dec (eIndex e) (eIndex x6)).
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. right. apply removeAfterIndex_le_In; auto.
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. left.
                find_copy_eapply_lem_hyp entries_sorted_invariant.
                find_eapply_lem_hyp maxIndex_le'; eauto;
                [|eapply entries_contiguous_invariant; eauto|eapply entries_contiguous_nw_invariant; eauto].
                find_copy_eapply_lem_hyp entries_contiguous_nw_invariant; eauto.
                unfold contiguous_range_exact_lo in *.
                break_and.
                find_copy_eapply_lem_hyp entries_sorted_invariant.
                match goal with
                  | H : forall _, _ < _ <= _ -> _ |- _ =>
                    specialize (H (eIndex e));
                      conclude_using ltac:(intuition; eapply le_trans; [eapply maxIndex_is_max; eauto|]; eauto)
                end.
                break_exists. break_and.
                match goal with
                  | H : eIndex ?x = eIndex e |- _ =>
                    copy_eapply entries_match_nw_host_invariant H
                end; eauto.
                find_copy_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                conclude_using
                  ltac:(match goal with
                          | H : _ |- _ => apply H
                        end; do_in_app; intuition;
                        match goal with
                          | H : In ?x _ |- In ?x _ =>
                            copy_eapply Prefix_maxIndex H
                        end; [|idtac|eauto]; eauto; omega).
                conclude_using eauto. conclude_using auto.
                match goal with
                  | H : _ = _ |- _ =>
                    eapply uniqueIndices_elim_eq in H
                end; eauto; eauto using sorted_uniqueIndices.
                subst. auto.
            - break_exists. break_and.
              destruct (le_lt_dec (eIndex e) (eIndex x6)).
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. right. apply removeAfterIndex_le_In; auto.
              + match goal with
                  | _ : removeAfterIndex _ (eIndex ?e) = ?l |- _ =>
                    assert (In e l) by (repeat find_reverse_rewrite;
                                        eapply removeAfterIndex_le_In; auto)
                end.
                find_copy_eapply_lem_hyp entries_sorted_invariant.
                assert (exists e', eIndex e' = eIndex e /\ In e' (x1 ++ x2)) by
                      (eapply entries_contiguous_nw_invariant; eauto;
                       intuition;
                       eapply le_trans; [eapply maxIndex_is_max; eauto|];
                       eapply maxIndex_le'; eauto;
                       [eapply entries_contiguous_invariant; eauto|
                        eapply entries_contiguous_nw_invariant; eauto]).
                do_in_app. intuition.
                * break_exists. break_and.
                  match goal with
                    | H : eIndex _ = eIndex _ |- _ =>
                      copy_eapply sorted_app_sorted_app_in1_in2_prefix H
                  end; eauto.
                  all:try solve [repeat find_reverse_rewrite; eauto using removeAfterIndex_sorted].
                  all:try solve [eapply entries_sorted_nw_invariant; eauto].
                  find_apply_hyp_hyp.
                  match goal with
                    | H : In e _ -> False |- _ => apply H
                  end.
                  apply in_app_iff. left.
                  match goal with
                    | H : eIndex _ = eIndex _ |- _ =>
                      copy_eapply entries_match_nw_host_invariant H
                  end; eauto. concludes. repeat conclude_using eauto.
                  match goal with
                    | H : eIndex _ = eIndex _ |- _ =>
                      copy_eapply uniqueIndices_elim_eq H
                  end; eauto using sorted_uniqueIndices. subst. auto.
                * find_copy_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                  unfold Prefix_sane in *.
                  intuition; [|find_eapply_lem_hyp maxIndex_is_max; eauto; omega].
                  find_eapply_lem_hyp prefix_contiguous. Focus 2. eauto.
                  all:eauto.
                  all:try solve [eapply contiguous_app; [|eapply entries_contiguous_nw_invariant; eauto];
                                 eapply entries_sorted_nw_invariant; eauto].
                  match goal with
                    | H : In e _ -> False |- _ => apply H
                  end. intuition.
            - subst.
              destruct (le_lt_dec (eIndex e) (eIndex x6)).
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. right. apply removeAfterIndex_le_In; auto.
              + match goal with
                  | _ : removeAfterIndex _ (eIndex ?e) = ?l |- _ =>
                    assert (In e l) by (repeat find_reverse_rewrite;
                                        eapply removeAfterIndex_le_In; auto)
                end.
                find_copy_eapply_lem_hyp entries_sorted_invariant.
                assert (exists e', eIndex e' = eIndex e /\ In e' (x1 ++ x4)) by
                      (eapply entries_contiguous_nw_invariant; eauto;
                       intuition;
                       eapply le_trans; [eapply maxIndex_is_max; eauto|];
                       eapply maxIndex_le'; eauto;
                       [eapply entries_contiguous_invariant; eauto|
                        eapply entries_contiguous_nw_invariant; eauto]).
                do_in_app. intuition.
                * break_exists. break_and.
                  match goal with
                    | H : eIndex _ = eIndex _ |- _ =>
                      copy_eapply sorted_app_sorted_app_in1_in2 H
                  end; eauto.
                  all:try solve [repeat find_reverse_rewrite; eauto using removeAfterIndex_sorted].
                  all:try solve [eapply entries_sorted_nw_invariant; eauto].
                  find_apply_hyp_hyp.
                  match goal with
                    | H : In e _ -> False |- _ => apply H
                  end.
                  apply in_app_iff. left.
                  match goal with
                    | H : eIndex _ = eIndex _ |- _ =>
                      copy_eapply entries_match_nw_host_invariant H
                  end; eauto. concludes. repeat conclude_using eauto.
                  match goal with
                    | H : eIndex _ = eIndex _ |- _ =>
                      copy_eapply uniqueIndices_elim_eq H
                  end; eauto using sorted_uniqueIndices. subst. auto.
                * match goal with
                    | H : In e _ -> False |- _ => apply H
                  end. intuition.
          }
        * { exfalso.
            find_copy_apply_lem_hyp append_entries_leaderLogs_invariant; eauto.
            break_exists; intuition.
            copy_eapply_prop_hyp append_entries_leaderLogs pBody; eauto.
            break_exists; break_and.
            subst. 
            find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
            conclude_using eauto. subst.
            match goal with
              | H : In _ _ -> False |- _ =>
                apply H
            end.
            find_copy_apply_lem_hyp leaderLogs_sorted_invariant; auto.
            find_copy_apply_lem_hyp maxIndex_is_max; auto. 
            destruct (le_lt_dec (eIndex e) (eIndex x1));
              [apply in_app_iff; right; eapply removeAfterIndex_le_In; eauto|].
            repeat find_rewrite. apply in_app_iff; intuition.
            - omega.
            - break_exists; break_and.
              unfold Prefix_sane in *. break_or_hyp; try omega.
              left; apply in_app_iff; right.
              eapply prefix_contiguous; eauto.
              eapply contiguous_app; [|eapply entries_contiguous_nw_invariant; eauto];
              eapply entries_sorted_nw_invariant; eauto.
            - subst. intuition.
          }
    - find_copy_eapply_lem_hyp allEntries_term_sanity_invariant; eauto.
      destruct (lt_eq_lt_dec t0 t); intuition; unfold ghost_data in *; simpl in *; try omega.
      + match goal with
          | H : context [pBody] |- _ =>
            copy_eapply append_entries_leaderLogs_invariant H
        end; eauto.
        break_exists. break_and. subst.
        match goal with
          | H : In (?t, ?ll) (leaderLogs (fst (nwState _ ?leader))) |- _ =>
            (exists t, leader, ll)
        end.
        split;
          [find_higher_order_rewrite;
            destruct_update; simpl in *;
            eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto|];
          split; auto. intuition; subst.
        * find_false.
          apply in_app_iff. right. eapply removeAfterIndex_le_In; eauto.
          find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
          eapply le_trans; [eapply maxIndex_is_max; eauto|]. omega.
        * {
            break_exists. intuition. unfold Prefix_sane in *. intuition.
            - destruct (le_lt_dec (eIndex e) (eIndex x4)).
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. right. apply removeAfterIndex_le_In; auto.
              + match goal with
                  | H : In e _ -> False |- _ => apply H
                end.
                apply in_app_iff. left.
                apply in_app_iff. right.
                find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                eapply prefix_contiguous; eauto.
                find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
                eapply contiguous_app; eauto.
                eapply entries_contiguous_nw_invariant; eauto.
            - find_false.
              repeat find_rewrite.
              apply in_app_iff. right.
              find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
              apply removeAfterIndex_le_In; auto.
              eapply maxIndex_is_max; eauto.
          }
        * find_false. intuition.
      + subst.
        find_eapply_lem_hyp allEntries_leaderLogs_term_invariant; eauto. intuition.
        * { subst. exfalso.
            find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
            find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
            break_exists. break_and.
            find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto.
            repeat find_rewrite.
            conclude_using eauto. subst.
            find_eapply_lem_hyp le_antisym; eauto.
            destruct x1.
            - simpl in *. destruct x2; simpl in *; auto.
              break_match; auto.
              match goal with
                | H : _ \/ (exists _, _) \/ _ |- _ =>
                  clear H
              end.
              break_and. subst.
              cut (e1 = x6); intros; subst; auto.
              find_apply_lem_hyp findAtIndex_elim.
              break_and.
              find_copy_apply_lem_hyp entries_sorted_invariant.
              eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices.
              eapply removeAfterIndex_in with (i := (eIndex e)).
              unfold raft_data, ghost_data in *; simpl in *.
              unfold raft_data, ghost_data in *; simpl in *.
              repeat find_rewrite. intuition.
            - simpl in *.
              match goal with
                | H : forall _, ?e = _ \/ _ -> _ |- _ =>
                  specialize (H e)
              end. conclude_using auto.
              repeat find_rewrite.
              find_apply_lem_hyp findAtIndex_elim. break_and.
              find_eapply_lem_hyp term_ne_in_l2. Focus 7. eauto. all:eauto.
              all:try solve [eapply entries_sorted_invariant; eauto].
              all:try solve [intros; find_eapply_lem_hyp no_entries_past_current_term_host_lifted_invariant; unfold ghost_data, raft_data in *; simpl in *;
                             unfold ghost_data, raft_data in *; simpl in *;
                             repeat find_rewrite; eauto].
              assert (eIndex e0 <= maxIndex x4) by 
                  (repeat find_rewrite;
                   eapply maxIndex_is_max; eauto;
                   eapply leaderLogs_sorted_invariant; eauto).
              assert (eIndex x7 < eIndex e0) by
                  (eapply entries_contiguous_nw_invariant; eauto; intuition).
              intuition.
              + break_exists. break_and.
                unfold Prefix_sane in *. intuition.
                find_copy_eapply_lem_hyp Prefix_maxIndex_eq; eauto.
                find_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
                find_eapply_lem_hyp sorted_gt_maxIndex; eauto; omega.
              + subst.
                find_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
                find_eapply_lem_hyp sorted_gt_maxIndex; eauto; try omega.
                destruct x4; simpl in *; congruence.
          }
        * { exfalso.
            find_copy_apply_lem_hyp append_entries_leaderLogs_invariant; eauto.
            break_exists; intuition. subst.
            copy_eapply_prop_hyp append_entries_leaderLogs pBody; eauto.
            break_exists; break_and.
            subst. 
            find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto;
            conclude_using eauto. subst.
            match goal with
              | H : In _ _ -> False |- _ =>
                apply H
            end.
            find_copy_apply_lem_hyp leaderLogs_sorted_invariant; auto.
            find_copy_apply_lem_hyp maxIndex_is_max; auto. 
            destruct (le_lt_dec (eIndex e) (eIndex x2));
              [apply in_app_iff; right; eapply removeAfterIndex_le_In; eauto|].
            repeat find_rewrite. apply in_app_iff; intuition.
            - omega.
            - break_exists; break_and.
              unfold Prefix_sane in *. break_or_hyp; try omega.
              left; apply in_app_iff; right.
              eapply prefix_contiguous; eauto.
              eapply contiguous_app; [|eapply entries_contiguous_nw_invariant; eauto];
              eapply entries_sorted_nw_invariant; eauto.
            - subst. intuition.
          }
  Qed.

  Lemma handleAppendEntriesReply_currentTerm_leaderId :
    forall h st h' t es res st' m,
      handleAppendEntriesReply h st h' t es res = (st', m) ->
      currentTerm st < currentTerm st' \/
      (currentTerm st = currentTerm st' /\ leaderId st' = leaderId st).
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat (break_match; try find_inversion; simpl in *; auto).
  Qed.

  Lemma allEntries_log_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_log.
    find_apply_lem_hyp handleAppendEntriesReply_currentTerm_leaderId.
    destruct_update; simpl in *; eauto; find_apply_hyp_hyp; repeat find_rewrite; intuition;
    right; break_exists_exists; repeat find_rewrite; intuition;
    find_higher_order_rewrite;
    destruct_update; simpl in *; auto.
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

  Lemma update_elections_data_requestVoteReply_leaderLogs :
    forall h h' t  st t' ll' r,
      In (t', ll') (leaderLogs (fst st)) ->
      In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; auto.
    simpl in *. intuition.
  Qed.

  Lemma allEntries_log_request_vote :
    refined_raft_net_invariant_request_vote allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleRequestVote_log.
    find_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
    destruct_update; simpl in *; eauto;
    try find_rewrite_lem update_elections_data_requestVote_allEntries;
    find_apply_hyp_hyp; repeat find_rewrite; intuition;
    right; break_exists_exists; intuition; repeat find_higher_order_rewrite;
    destruct_update; simpl in *; auto;
    rewrite update_elections_data_requestVote_leaderLogs; auto.
  Qed.

  Lemma handleRequestVoteReply_log' :
    forall h st h' t r,
      log (handleRequestVoteReply h st h' t r) = log st.
  Proof.
    eauto using handleRequestVoteReply_log.
  Qed.

  Lemma allEntries_log_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    find_copy_apply_lem_hyp handleRequestVoteReply_currentTerm_leaderId.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    try rewrite handleRequestVoteReply_log';
    try find_rewrite_lem update_elections_data_requestVoteReply_allEntries;
    find_apply_hyp_hyp; repeat find_rewrite; intuition;
    right; break_exists_exists; repeat find_rewrite; intuition;
    find_higher_order_rewrite;
    destruct_update; simpl in *; auto;
    apply update_elections_data_requestVoteReply_leaderLogs; auto.
  Qed.

  Lemma update_elections_data_client_request_allEntries' :
    forall h st client id c out st' ms t e,
      handleClientRequest h (snd st) client id c = (out, st', ms) ->
      In (t, e) (allEntries (update_elections_data_client_request h st client id c)) ->
      In (t, e) (allEntries (fst st)) \/
      In e (log st').
  Proof.
    intros.
    unfold update_elections_data_client_request in *.
    repeat break_match; repeat find_inversion; auto.
    simpl in *. intuition.
    find_inversion. repeat find_rewrite. intuition.
  Qed.

  Lemma handleClientRequest_currentTerm_leaderId :
    forall h st client id c out st' ms,
      handleClientRequest h st client id c = (out, st', ms) ->
      currentTerm st' = currentTerm st /\
      leaderId st' = leaderId st.
  Proof.
    intros. unfold handleClientRequest in *.
    subst.
    break_match; try find_inversion; simpl in *; auto.
  Qed.
  
  Lemma allEntries_log_client_request :
    refined_raft_net_invariant_client_request allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *;
    try (find_eapply_lem_hyp update_elections_data_client_request_allEntries'; eauto; [idtac]);
    intuition;
    find_copy_apply_lem_hyp handleClientRequest_log;
    find_apply_lem_hyp handleClientRequest_currentTerm_leaderId;
    intuition;
    try break_exists; intuition; repeat find_rewrite; intuition; simpl in *;
    find_apply_hyp_hyp; intuition; repeat right;
    break_exists_exists; intuition;
    repeat find_higher_order_rewrite;
    destruct_update; simpl in *; auto;
    rewrite update_elections_data_client_request_leaderLogs; auto.
  Qed.

  Lemma handleTimeout_currentTerm_leaderId :
    forall h st out st' ms,
      handleTimeout h st = (out, st', ms) ->
      currentTerm st < currentTerm st' \/
      currentTerm st' = currentTerm st /\ leaderId st' = leaderId st.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    subst.
    break_match; try find_inversion; simpl in *; auto.
  Qed.
  
  Lemma allEntries_log_timeout :
    refined_raft_net_invariant_timeout allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *;
    try find_rewrite_lem update_elections_data_timeout_allEntries;
    find_copy_apply_lem_hyp handleTimeout_log_same;
    find_apply_lem_hyp handleTimeout_currentTerm_leaderId;
    repeat find_rewrite;
    find_apply_hyp_hyp; intuition;
    right; break_exists_exists; intuition;
    repeat find_higher_order_rewrite;
    destruct_update; simpl in *; auto;
    rewrite update_elections_data_timeout_leaderLogs; auto.
  Qed.

  Lemma doLeader_currentTerm_leaderId :
    forall st h out st' m,
      doLeader st h = (out, st', m) ->
      currentTerm st' = currentTerm st /\
      leaderId st' = leaderId st.
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; simpl in *; auto.
  Qed.
  
  Lemma allEntries_log_do_leader :
    refined_raft_net_invariant_do_leader allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp doLeader_log.
    find_apply_lem_hyp doLeader_currentTerm_leaderId.
    destruct_update; simpl in *; eauto; find_apply_hyp_hyp; repeat find_rewrite; intuition;
    right; break_exists_exists; intuition; find_higher_order_rewrite;
    destruct_update; simpl in *; auto.
  Qed.


  Lemma doGenericServer_currentTerm_leaderId :
    forall st h out st' m,
      doGenericServer h st = (out, st', m) ->
      currentTerm st' = currentTerm st /\
      leaderId st' = leaderId st.
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion;
    use_applyEntries_spec; subst; simpl in *;
    auto.
  Qed.
  
  Lemma allEntries_log_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp doGenericServer_log.
    find_apply_lem_hyp doGenericServer_currentTerm_leaderId.
    destruct_update; simpl in *; eauto; find_apply_hyp_hyp; repeat find_rewrite; intuition;
    right; break_exists_exists; intuition; find_higher_order_rewrite;
    destruct_update; simpl in *; auto.
  Qed.

  Lemma allEntries_log_init :
    refined_raft_net_invariant_init allEntries_log.
  Proof.
    red. unfold allEntries_log. intros. simpl in *. intuition.
  Qed.

  Lemma allEntries_log_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros.
    repeat find_reverse_higher_order_rewrite.
    find_apply_hyp_hyp. intuition. right.
    break_exists_exists. repeat find_higher_order_rewrite. auto.
  Qed.

  Lemma allEntries_log_reboot :
    refined_raft_net_invariant_reboot allEntries_log.
  Proof.
    red. unfold allEntries_log in *. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    repeat find_higher_order_rewrite.
    subst. unfold reboot in *.
    destruct_update; simpl in *; eauto; find_apply_hyp_hyp; repeat find_rewrite; intuition;
    right; break_exists_exists; intuition; find_higher_order_rewrite;
    destruct_update; simpl in *; auto.
  Qed.

  Lemma allEntries_log_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      allEntries_log net.
  Proof.
    intros. apply refined_raft_net_invariant; auto.
    - exact allEntries_log_init.
    - exact allEntries_log_client_request.
    - exact allEntries_log_timeout.
    - exact allEntries_log_append_entries.
    - exact allEntries_log_append_entries_reply.
    - exact allEntries_log_request_vote.
    - exact allEntries_log_request_vote_reply.
    - exact allEntries_log_do_leader.
    - exact allEntries_log_do_generic_server.
    - exact allEntries_log_state_same_packet_subset.
    - exact allEntries_log_reboot.
  Qed.

  Instance aeli : allEntries_log_interface.
  split. eauto using allEntries_log_invariant.
  Defined.
End AllEntriesLog.
