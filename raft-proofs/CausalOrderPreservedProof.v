Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import StructTact.Util.
Require Import StructTact.StructTactics.
Require Import TraceRelations.
Require Import UpdateLemmas.

Require Import Raft.
Require Import CommonTheorems.
Require Import TraceStructTact.Util.

Require Import CausalOrderPreservedInterface.
Require Import OutputImpliesAppliedInterface.
Require Import AppliedImpliesInputInterface.
Require Import AppliedEntriesMonotonicInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section CausalOrderPreserved.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.
  Context {aiii : applied_implies_input_interface}.
  Context {aemi : applied_entries_monotonic_interface}.

  Section inner.
  Variables client id client' id' : nat.

  Lemma before_func_app_necessary :
    forall A f g (l : list A) l',
      ~ before_func f g l ->
      before_func f g (l ++ l') ->
      (forall x, In x l -> g x = false) /\
      before_func f g l'.
  Proof.
    intros. induction l; simpl in *; intuition; subst; auto.
  Qed.

  Lemma output_before_input_not_key_in_input_trace :
    forall tr tr' s s',
      ~ output_before_input client id client' id' tr ->
      step_f s s' tr' ->
      output_before_input client id client' id' (tr ++ tr') ->
      ~ exists i, in_input_trace client' id' i (tr ++ tr').
  Proof.
    intros. find_eapply_lem_hyp before_func_app_necessary; eauto.
    intuition.
    break_exists. unfold in_input_trace in *.
    break_exists. do_in_app. intuition;
      [find_apply_hyp_hyp; simpl in *; repeat (do_bool; intuition)|].
    invcs H0; intuition.
    - break_if; congruence.
    - find_inversion; try congruence.
      repeat (do_bool; intuition).
    - find_inversion.
  Qed.


  Lemma output_before_input_key_in_output_trace :
    forall tr,
      output_before_input client id client' id' tr ->
      key_in_output_trace client id tr.
  Proof.
    intros. unfold output_before_input in *.
    induction tr; simpl in *; intuition.
    - unfold key_in_output_trace.
      unfold is_output_with_key in *. repeat break_match; try congruence.
      subst. do 2 eexists. intuition; eauto.
    - unfold key_in_output_trace in *.
      break_exists_exists. simpl; intuition.
  Qed.

  Lemma in_applied_entries_entries_ordered :
    forall net,
      in_applied_entries client id net ->
      ~ in_applied_entries client' id' net ->
      entries_ordered client id client' id' net.
  Proof.
    intros. unfold in_applied_entries, entries_ordered in *.
    induction (applied_entries (nwState net)); simpl in *; break_exists; intuition.
    - subst. left. unfold has_key. break_match.
      simpl. repeat (do_bool; intuition).
    - right. intuition.
      + apply Bool.not_true_iff_false. intuition.
        find_false.
        unfold has_key in *. break_match; simpl in *; repeat (do_bool; intuition).
        subst. eexists; intuition; eauto.
      + eapply IHl.
        * eexists; intuition; eauto.
        * intuition. find_false. break_exists_exists. intuition.
  Qed.


  Lemma in_applied_entries_applied_implies_input_state :
    forall net,
      in_applied_entries client' id' net ->
      exists e,
        eClient e = client' /\
        eId e = id' /\
        applied_implies_input_state client' id' (eInput e) net.
  Proof.
    intros.
    unfold in_applied_entries in *. break_exists_exists.
    intuition. red. exists x. intuition.
    - red. auto.
    - unfold applied_entries in *. break_match.
      + find_apply_lem_hyp in_rev.
        find_apply_lem_hyp removeAfterIndex_in.
        eauto.
      + simpl in *. intuition.
  Qed.
  
  Instance TR : TraceRelation step_f :=
    {
      init := step_f_init;
      T := output_before_input client id client' id';
      R := fun s => entries_ordered client id client' id' (snd s)
    }.
  Proof.
    - intros.
      unfold output_before_input.
      eapply before_func_dec.
    - intros.
      destruct s as (failed, net).
      destruct s' as (failed', net'). simpl in *.
      unfold entries_ordered in *.
      find_apply_lem_hyp step_f_star_raft_intermediate_reachable.
      find_eapply_lem_hyp applied_entries_monotonic'; eauto.
      break_exists; repeat find_rewrite.
      eauto using before_func_app.
    - intuition.
    - intros.
      destruct s as (failed, net).
      destruct s' as (failed', net'). simpl in *.
      find_copy_eapply_lem_hyp output_before_input_not_key_in_input_trace; eauto.
      find_copy_apply_lem_hyp output_before_input_key_in_output_trace.
      find_eapply_lem_hyp output_implies_applied;
        [|eapply refl_trans_n1_1n_trace; econstructor; eauto using refl_trans_1n_n1_trace].
      eapply in_applied_entries_entries_ordered; auto.
      intuition.
      find_false.
      find_apply_lem_hyp in_applied_entries_applied_implies_input_state.
      break_exists. intuition.
      eexists. eapply applied_implies_input; eauto.
      eapply refl_trans_n1_1n_trace; econstructor; eauto using refl_trans_1n_n1_trace.
  Defined.

  Theorem causal_order_preserved :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      output_before_input client id client' id' tr ->
      entries_ordered client id client' id' net.
  Proof.
    intros. pose proof (trace_relations_work (failed, net) tr).
    concludes. intuition.
  Qed.

  End inner.

  Instance copi : causal_order_preserved_interface.
  Proof.
    split.
    intros.
    eapply causal_order_preserved; eauto.
  Qed.
End CausalOrderPreserved.
