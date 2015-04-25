Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import StateMachineCorrectInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.

Section StateMachineCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

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

  Definition clientCache_to_ks (c : list (nat * (nat * output))) :=
    map (fun e => (fst e, fst (snd e))) c.

  Lemma snd_execute_log' :
    forall l st o o',
      snd (execute_log' l st o) = snd (execute_log' l st o').
  Proof.
    induction l; intros; simpl in *; intuition;
    break_let; eauto.
  Qed.


  Lemma snd_execute_log'_nil :
    forall l st o,
      snd (execute_log' l st o) = snd (execute_log' l st []).
  Proof.
    eauto using snd_execute_log'.
  Qed.
  
  Lemma clientCache_to_ks_assoc :
    forall c client id,
      assoc eq_nat_dec (clientCache_to_ks c) client = Some id ->
      exists o,
        assoc eq_nat_dec c client = Some (id, o).
  Proof.
    induction c; intros; simpl in *; try congruence.
    break_if; eauto.
    - subst. find_inversion.
      break_let. subst. simpl in *. break_if; try congruence.
      destruct p. simpl in *. eauto.
    - break_let; subst; simpl in *. break_if; try congruence. eauto.
  Qed.

  Lemma clientCache_to_ks_assoc_getLastId :
    forall st client id,
      assoc eq_nat_dec (clientCache_to_ks (clientCache st)) client = Some id ->
      exists o,
        getLastId st client = Some (id, o).
  Proof.
    eauto using clientCache_to_ks_assoc.
  Qed.

  Lemma clientCache_to_ks_assoc_none :
    forall c client,
      assoc eq_nat_dec (clientCache_to_ks c) client = None ->
      assoc eq_nat_dec c client = None.
  Proof.
    induction c; intros; simpl in *; try congruence.
    break_if; eauto; try congruence.
    - break_let; subst; simpl in *. break_if; try congruence. eauto.
  Qed.

  Lemma clientCache_to_ks_assoc_getLastId_none :
    forall st client,
      assoc eq_nat_dec (clientCache_to_ks (clientCache st)) client = None ->
      getLastId st client = None.
  Proof.
    eauto using clientCache_to_ks_assoc_none.
  Qed.
  
  Lemma cacheApplyEntry_stateMachine_apply :
    forall st e os st' id o o' d,
      cacheApplyEntry st e = (os, st') ->
      getLastId st (eClient e) = Some (id, o) ->
      id < eId e ->
      handler (eInput e) (stateMachine st) = (o', d) ->
      stateMachine st' = d.
  Proof.
    intros.
    unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; subst; repeat find_inversion; do_bool; try omega;
    simpl in *; auto.
  Qed.

  Lemma cacheApplyEntry_cache_apply :
    forall st e os st' id o o' d,
      cacheApplyEntry st e = (os, st') ->
      getLastId st (eClient e) = Some (id, o) ->
      id < eId e ->
      handler (eInput e) (stateMachine st) = (o', d) ->
      assoc_set eq_nat_dec (clientCache st) (eClient e) (eId e, o') = clientCache st'.
  Proof.
    intros.
    unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; subst; repeat find_inversion; do_bool;
    simpl in *; auto; omega.
  Qed.


  Lemma cacheApplyEntry_stateMachine_apply_none :
    forall st e os st' o' d,
      cacheApplyEntry st e = (os, st') ->
      getLastId st (eClient e) = None ->
      handler (eInput e) (stateMachine st) = (o', d) ->
      stateMachine st' = d.
  Proof.
    intros.
    unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; subst; repeat find_inversion; do_bool; try omega;
    simpl in *; auto; congruence.
  Qed.

  Lemma cacheApplyEntry_cache_apply_none :
    forall st e os st' o' d,
      cacheApplyEntry st e = (os, st') ->
      getLastId st (eClient e) = None ->
      handler (eInput e) (stateMachine st) = (o', d) ->
      assoc_set eq_nat_dec (clientCache st) (eClient e) (eId e, o') = clientCache st'.
  Proof.
    intros.
    unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; subst; repeat find_inversion; do_bool;
    simpl in *; auto; congruence.
  Qed.

  Lemma cacheApplyEntry_stateMachine_no_apply :
    forall st e os st' id o,
      cacheApplyEntry st e = (os, st') ->
      getLastId st (eClient e) = Some (id, o) ->
      eId e <= id ->
      stateMachine st' = stateMachine st.
  Proof.
    intros.
    unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; subst; repeat find_inversion; do_bool;
    simpl in *; auto; try omega; congruence.
  Qed.

  Lemma cacheApplyEntry_cache_no_apply :
    forall st e os st' id o,
      cacheApplyEntry st e = (os, st') ->
      getLastId st (eClient e) = Some (id, o) ->
      eId e <= id ->
      clientCache st = clientCache st'.
  Proof.
    intros.
    unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; subst; repeat find_inversion; do_bool;
    simpl in *; auto; try omega; congruence.
  Qed.
  
  Lemma clientCache_to_ks_assoc_set :
    forall c client id o,
      assoc_set eq_nat_dec (clientCache_to_ks c) client id =
      clientCache_to_ks (assoc_set eq_nat_dec c client (id, o)).
  Proof.
    induction c; intros; simpl in *; intuition.
    simpl.
    break_if; simpl in *; eauto.
    f_equal. eauto.
  Qed.
  
  Lemma applyEntries_execute_log' :
    forall l h st os st',
      applyEntries h st l = (os, st') ->
      stateMachine st' = (snd (execute_log'
                                 (deduplicate_log' l (clientCache_to_ks (clientCache st)))
                                 (stateMachine st) [])).
  Proof.
    induction l; intros; simpl in *; intuition.
    - find_inversion. auto.
    - repeat break_let. find_inversion.
      repeat break_match; simpl in *.
      + break_let.
        rewrite snd_execute_log'_nil.
        find_apply_hyp_hyp. do_bool.
        find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
        break_exists.
        find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply;
          [|eauto|idtac|]; eauto. subst.
        find_eapply_lem_hyp cacheApplyEntry_cache_apply; eauto.
        erewrite clientCache_to_ks_assoc_set.
        rewrite Heqp1. eauto.
      + do_bool.
        find_apply_hyp_hyp.
        find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
        break_exists.
        break_exists.
        find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_no_apply; eauto.
        find_eapply_lem_hyp cacheApplyEntry_cache_no_apply; eauto.
        repeat find_rewrite. auto.
      + break_let. 
        rewrite snd_execute_log'_nil.
        find_apply_hyp_hyp. do_bool.
        find_apply_lem_hyp clientCache_to_ks_assoc_getLastId_none.
        break_exists.
        find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply_none; eauto.
        subst.
        find_eapply_lem_hyp cacheApplyEntry_cache_apply_none; eauto.
        erewrite clientCache_to_ks_assoc_set.
        rewrite Heqp1. eauto.
  Qed.
  
  Lemma state_machine_do_generic_server :
    raft_net_invariant_do_generic_server state_machine_correct.
  Proof.
    red. unfold state_machine_correct. intros.
    intuition.
    - unfold state_machine_log in *. simpl in *. intros.
      find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      unfold doGenericServer in *. break_let.
      find_inversion. simpl in *.
      find_apply_lem_hyp applyEntries_execute_log'. repeat find_rewrite.
      simpl in *. repeat find_higher_order_rewrite.
      unfold client_cache_complete in *.
  Admitted.
      

  Theorem state_machine_correct_invariant :
    forall net,
      raft_intermediate_reachable net ->
      state_machine_correct net.
  Admitted.

  Instance smci : state_machine_correct_interface.
  Proof.
    split.
    exact state_machine_correct_invariant.
  Qed.
End StateMachineCorrect.
