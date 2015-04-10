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

Require Import AllEntriesVotesWithLogInterface.
Require Import LogsLeaderLogsInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import RefinedLogMatchingLemmasInterface.
Require Import AllEntriesLeaderLogsTermInterface.
Require Import LeaderLogsContiguousInterface.
Require Import OneLeaderLogPerTermInterface.

Section AllEntriesVotesWithLog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {llli : logs_leaderLogs_interface}.
  Context {aerlli : append_entries_leaderLogs_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {aellti : allEntries_leaderLogs_term_interface}.
  Context {llci : leaderLogs_contiguous_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.

  Definition allEntries_log (net : network) : Prop :=
    forall t e h,
      In (t, e) (allEntries (fst (nwState net h))) ->
      In e (log (snd (nwState net h))) \/
      (exists t' leader ll,
         In (t', ll) (leaderLogs (fst (nwState net leader))) /\
         t < t' /\
         ~ In e ll).


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

  Lemma allEntries_term_sanity_invariant :
    forall net t e h,
      refined_raft_intermediate_reachable net ->
      In (t, e) (allEntries (fst (nwState net h))) ->
      t <= currentTerm (snd (nwState net h)).
  Proof.
    admit.
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
    find_copy_apply_hyp_hyp.
    intuition; [|right; break_exists_exists; intuition;
                 repeat find_higher_order_rewrite;
                 destruct_update; simpl in *;
                 eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto].
    destruct (in_dec entry_eq_dec e (log d)); intuition.
    right.
    find_apply_lem_hyp handleAppendEntries_log_detailed. intuition; repeat find_rewrite; intuition.
    - subst.
      find_copy_eapply_lem_hyp allEntries_term_sanity_invariant; eauto.
      destruct (lt_eq_lt_dec t0 t); intuition; unfold ghost_data in *; simpl in *; try omega.
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
          split; auto.
        intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
        subst.
        match goal with
          | H : In _ _ -> False |- _ =>
            apply H
        end.
        repeat find_rewrite.
        intuition.
      + subst.
        find_eapply_lem_hyp allEntries_leaderLogs_term_invariant. intuition.
        * subst. exfalso.
          find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
          find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
          break_exists; intuition;
          [break_exists; intuition;
           find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto; omega|].
          subst. clean.
          find_eapply_lem_hyp one_leaderLog_per_term_invariant; eauto;
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
          assert (exists e', eIndex e' = eIndex e /\ In e' (x1 ++ x4)).
          eapply entries_contiguous_nw_invariant; eauto.
          intuition; [eapply entries_contiguous_invariant; eauto|].
  Admitted.
        
  Instance aevwli : allEntries_votesWithLog_interface.
  Admitted.
End AllEntriesVotesWithLog.
