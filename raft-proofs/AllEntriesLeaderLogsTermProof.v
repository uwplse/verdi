Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import RefinementSpecLemmas.

Require Import AllEntriesLeaderLogsTermInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.

Section AllEntriesLeaderLogsTerm.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {aerlli : append_entries_leaderLogs_interface}.

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

  Lemma allEntries_leaderLogs_term_append_entries :
    refined_raft_net_invariant_append_entries allEntries_leaderLogs_term.
  Proof.
    red. unfold allEntries_leaderLogs_term. intros. simpl in *. subst.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *;
    [|find_apply_hyp_hyp; intuition;
      right; break_exists_exists; intuition;
      find_higher_order_rewrite;
      destruct_update; simpl in *; eauto;
      rewrite update_elections_data_appendEntries_leaderLogs; eauto].
    find_apply_lem_hyp update_elections_data_appendEntries_allEntries_term.
    intuition;
      [find_apply_hyp_hyp; intuition;
       right; break_exists_exists; intuition;
       find_higher_order_rewrite;
       destruct_update; simpl in *; eauto;
       rewrite update_elections_data_appendEntries_leaderLogs; eauto|].
    subst.
    match goal with
      | H : context [pBody] |- _ =>
        eapply append_entries_leaderLogs_invariant in H; eauto
    end.
    break_exists. break_and. subst. do_in_app.
    break_or_hyp; try find_apply_hyp_hyp; auto.
    right.
    find_eapply_lem_hyp Prefix_In; eauto.
    repeat eexists; eauto.
    find_higher_order_rewrite;
      destruct_update; simpl in *; eauto;
      rewrite update_elections_data_appendEntries_leaderLogs; subst; eauto.
  Qed.

  (* rest of cases are easy *)
      
  Instance aellti : allEntries_leaderLogs_term_interface.
  Admitted.
End AllEntriesLeaderLogsTerm.
