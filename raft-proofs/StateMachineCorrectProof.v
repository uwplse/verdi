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
Require Import SortedInterface.

Section StateMachineCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {si : sorted_interface}.
  
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

  Lemma applyEntries_lastApplied_commitIndex_log :
    forall l h st os st',
      applyEntries h st l = (os, st') ->
      lastApplied st' = lastApplied st /\
      commitIndex st' = commitIndex st /\
      log st' = log st.
  Proof.
    induction l; simpl in *; intros.
    - find_inversion. auto.
    - repeat break_match; find_inversion; simpl in *;
      unfold cacheApplyEntry, applyEntry in *;
      repeat break_match; find_inversion; simpl in *; eauto;
      copy_eapply_prop_hyp applyEntries applyEntries; intuition; simpl in *; auto.
  Qed.
  
  Lemma filter_false :
    forall A (l : list A),
      filter (fun _ => false) l = [].
  Proof.
    intros. induction l; simpl in *; auto.
  Qed.

  Fixpoint log_to_ks' (l : list entry) ks :=
    match l with
      | e :: l' =>
        if (assoc_default eq_nat_dec ks (eClient e) 0) <=? eId e then
          log_to_ks' l' (assoc_set eq_nat_dec ks (eClient e) (eId e))
        else
          log_to_ks' l' ks
      | [] => ks
    end.
  
  Definition log_to_ks l := log_to_ks' l [].

  Lemma assoc_assoc_default:
    forall (K V : Type) K_eq_dec (l : list (K * V)) k v d,
      assoc K_eq_dec l k = Some v ->
      assoc_default K_eq_dec l k d = v.
  Proof.
    intros. unfold assoc_default.
    break_match; congruence.
  Qed.

  Lemma assoc_assoc_default_missing:
    forall (K V : Type) K_eq_dec (l : list (K * V)) k d,
      assoc K_eq_dec l k = None ->
      assoc_default K_eq_dec l k d = d.
  Proof.
    intros. unfold assoc_default.
    break_match; congruence.
  Qed.

  Lemma assoc_set_same :
    forall (K V : Type) K_eq_dec (l : list (K * V)) k v,
      assoc K_eq_dec l k = Some v ->
      assoc_set K_eq_dec l k v = l.
  Proof.
    intros. induction l; simpl in *; auto; try congruence.
    repeat break_match; simpl in *; intuition.
    - subst. find_inversion. auto.
    - repeat find_rewrite. auto.
  Qed.

  Lemma deduplicate_log'_app :
    forall l1 l2 ks,
      deduplicate_log' (l1 ++ l2) ks =
      deduplicate_log' l1 ks ++ (deduplicate_log' l2 (log_to_ks' l1 ks)).
  Proof.
    induction l1; intros; simpl in *; auto.
    repeat break_match; simpl in *; eauto; try solve [f_equal; eauto].
    - exfalso. do_bool.
      find_erewrite_lem assoc_assoc_default. omega.
    - do_bool.
      find_erewrite_lem assoc_assoc_default.
      rewrite assoc_set_same; eauto.
      find_eapply_lem_hyp le_antisym; eauto. subst. auto.
    - exfalso. do_bool.
      find_erewrite_lem assoc_assoc_default_missing. omega.
  Qed.

  Lemma filter_and :
    forall A (l : list A) f g,
      (forall x, In x l -> f x = true) ->
      filter (fun x => f x && g x) l = filter (fun x => g x) l.
  Proof.
    intros. induction l; simpl in *; auto.
    repeat break_if; do_bool; simpl in *; auto.
    - f_equal; eauto.
    - intuition. congruence.
    - intuition; try congruence.
      assert (f a = true) by eauto.
      congruence.
  Qed.
  
  Lemma removeAfterIndex_app :
    forall l i i',
      sorted l ->
      i' < i ->
      removeAfterIndex l i =
      filter (fun x => eIndex x <=? i) (findGtIndex l i') ++ removeAfterIndex l i'.
  Proof.
    intros. induction l; simpl in *; auto.
    repeat (break_match; simpl in *); do_bool; intuition; try omega; try congruence.
    f_equal. repeat find_reverse_rewrite.
    rewrite removeAfterIndex_eq; auto.
    intros. find_apply_hyp_hyp. omega.
  Qed.

  Definition client_cache_keys_correct net :=
    forall h,
      clientCache_to_ks (clientCache (nwState net h)) =
      log_to_ks'
        (rev
           (removeAfterIndex (log (nwState net h))
                             (lastApplied (nwState net h)))) [].
    
  Lemma client_cache_keys_correct_invariant:
    forall (net : network),
      raft_intermediate_reachable net ->
      client_cache_keys_correct net.
  Proof.
  Admitted.

  Lemma log_to_ks'_app :
    forall l1 l2 ks,
      log_to_ks' (l1 ++ l2) ks = log_to_ks' l2 (log_to_ks' l1 ks).
  Proof.
    induction l1; intros; simpl in *; auto.
    break_if; simpl in *; eauto.
  Qed.

  Lemma assoc_default_assoc_set :
    forall K V K_eq_dec l (k : K) (v : V) d,
      assoc_default K_eq_dec (assoc_set K_eq_dec l k v) k d = v.
  Proof.
    intros. unfold assoc_default.
    rewrite get_set_same. auto.
  Qed.

  Lemma assoc_set_assoc_set_same :
    forall K V K_eq_dec l (k : K) (v : V) v',
      assoc_set K_eq_dec (assoc_set K_eq_dec l k v) k v' = assoc_set K_eq_dec l k v'.
  Proof.
    induction l; intros; simpl in *; repeat break_match; simpl in *; subst; try congruence; eauto;
    break_if; congruence.
  Qed.

  Definition a_equiv {K V} K_eq_dec (l1 : list (K * V)) l2 :=
    forall k,
      assoc K_eq_dec l1 k = assoc K_eq_dec l2 k.

  Lemma assoc_set_assoc_set_diff :
    forall K V K_eq_dec l (k : K) (v : V) k' v',
      k <> k' ->
      a_equiv K_eq_dec (assoc_set K_eq_dec (assoc_set K_eq_dec l k v) k' v')
              (assoc_set K_eq_dec (assoc_set K_eq_dec l k' v') k v).
  Proof.
    unfold a_equiv;
    induction l; intros; simpl in *; repeat (break_match; simpl in *; try congruence).
    eauto.
  Qed.

  Lemma assoc_set_a_equiv :
    forall K V K_eq_dec l l' (k : K) (v : V),
      a_equiv K_eq_dec l l' ->
      a_equiv K_eq_dec (assoc_set K_eq_dec l k v) (assoc_set K_eq_dec l' k v).
  Proof.
    intros. induction l; simpl in *; auto.
    - unfold a_equiv in *. simpl in *.
      intros. break_if; subst; eauto using get_set_same, get_set_diff.
      rewrite get_set_diff; auto.
    - repeat break_match; subst; simpl in *; eauto.
      + unfold a_equiv. simpl in *. intros.
        break_match; simpl in *; subst; eauto using get_set_same.
        rewrite get_set_diff; eauto.
        unfold a_equiv in *. simpl in *.
        specialize (H k). break_if; congruence.
      + unfold a_equiv. simpl in *. intros.
        break_match; simpl in *; subst; eauto using get_set_same.
        * rewrite get_set_diff; eauto.
          unfold a_equiv in *.
          simpl in *. specialize (H k0). break_if; congruence.
        * { destruct (K_eq_dec k k1); subst.
            - repeat rewrite get_set_same. auto.
            - repeat rewrite get_set_diff; auto.
              specialize (H k1). simpl in *.
              break_if; congruence.
          }
  Qed.

  Lemma assoc_default_a_equiv :
    forall K V K_eq_dec l l' (k : K) (v : V),
      a_equiv K_eq_dec l l' ->
      assoc_default K_eq_dec l k v = assoc_default K_eq_dec l' k v.
  Proof.
    intros. unfold a_equiv, assoc_default in *.
    find_higher_order_rewrite.
    auto.
  Qed.

  Lemma log_to_ks'_a_equiv :
    forall l ks ks',
      a_equiv eq_nat_dec ks ks' ->
      a_equiv eq_nat_dec (log_to_ks' l ks) (log_to_ks' l ks').
  Proof.
    induction l; intros; simpl in *; auto.
    repeat break_match; simpl in *; eauto.
    - eapply IHl; eauto.
      eauto using assoc_set_a_equiv.
    - do_bool.
      match goal with
        | _ : ?x <= _, _ : _ < ?y |- _ =>
          assert (x = y) by eauto using assoc_default_a_equiv
      end. omega.
    - do_bool.
      match goal with
        | _ : ?x <= _, _ : _ < ?y |- _ =>
          assert (y = x) by eauto using assoc_default_a_equiv
      end. omega.
  Qed.

  Lemma log_to_ks'_assoc_default_ks :
    forall l ks c i,
      i <= assoc_default eq_nat_dec
                        (log_to_ks' l (assoc_set Nat.eq_dec ks c i))
                        c 0.
  Proof.
    induction l; intros; simpl in *; auto.
    - rewrite assoc_default_assoc_set. auto.
    - break_if; simpl in *; eauto.
      do_bool.
      destruct (eq_nat_dec (eClient a) c); simpl in *; auto.
      + subst.
        find_rewrite_lem assoc_default_assoc_set.
        rewrite assoc_set_assoc_set_same.
        eauto using le_trans.
      + erewrite assoc_default_a_equiv;
        [|eapply log_to_ks'_a_equiv;
           eapply assoc_set_assoc_set_diff; auto].
        eauto.
  Qed.
  
  Lemma assoc_default_assoc_set_diff :
    forall K V K_eq_dec (l : list (K * V)) k v k' d,
      k <> k' ->
      assoc_default K_eq_dec (assoc_set K_eq_dec l k' v) k d =
      assoc_default K_eq_dec l k d.
  Proof.
    intros. unfold assoc_default. rewrite get_set_diff; auto.
  Qed.

  Lemma log_to_ks'_assoc_default_assoc_default_le :
    forall l ks c,
      assoc_default eq_nat_dec ks c 0 <=
      assoc_default eq_nat_dec (log_to_ks' l ks) c 0.
  Proof.
    induction l; intros; simpl in *; auto.
    break_if; simpl in *; eauto.
    do_bool.
    destruct (eq_nat_dec (eClient a) c); simpl in *; subst; auto.
    - eapply le_trans; eauto.
      eauto using log_to_ks'_assoc_default_ks.
    - match goal with
        | [ |- context [ assoc_set ?e ?ks ?c' ?i ] ] =>
          assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c' i) c 0)
      end; repeat find_rewrite; eauto.
      rewrite assoc_default_assoc_set_diff; auto.
  Qed.

  Lemma log_to_ks'_assoc_default_eq :
    forall l ks ks' c,
      assoc_default eq_nat_dec (log_to_ks' l ks) c 0 <= assoc_default eq_nat_dec ks' c 0 ->
      assoc_default eq_nat_dec (log_to_ks' l ks') c 0 = assoc_default eq_nat_dec ks' c 0.
  Proof.
    induction l; intros; simpl in *; auto.
    repeat break_if; do_bool; simpl in *; eauto.
    - destruct (eq_nat_dec (eClient a) c); simpl in *; auto.
      + subst.
        match goal with
          | [ |- context [ assoc_set ?e ?ks ?c ?i ] ] =>
            assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c i) c 0)
        end; repeat find_rewrite; eauto.
        rewrite assoc_default_assoc_set.
        eapply le_antisym; eauto.
        eapply le_trans; [|eauto];
        eauto using log_to_ks'_assoc_default_ks.
      + match goal with
          | [ |- context [ assoc_set ?e ?ks ?c' ?i ] ] =>
            assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c' i) c 0)
        end; repeat find_rewrite; eauto.
        rewrite assoc_default_assoc_set_diff; auto.
    - destruct (eq_nat_dec (eClient a) c); simpl in *; auto.
      + subst.
        match goal with
          | [ |- context [ assoc_set ?e ?ks ?c ?i ] ] =>
            assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c i) c 0)
        end; repeat find_rewrite; eauto.
        rewrite assoc_default_assoc_set.
        eapply le_antisym; eauto.
        eapply le_trans; [|eauto];
        eauto using log_to_ks'_assoc_default_ks.
        eapply le_trans; [|eauto using log_to_ks'_assoc_default_assoc_default_le].
        omega.
      + match goal with
          | [ |- context [ assoc_set ?e ?ks ?c' ?i ] ] =>
            assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c' i) c 0)
        end; repeat find_rewrite; eauto.
        rewrite assoc_default_assoc_set_diff; auto.
  Qed.
  
  Lemma log_to_ks'_assoc_set_diff :
    forall l ks k v k',
      k <> k' ->
      assoc_default eq_nat_dec
                    (log_to_ks' l (assoc_set Nat.eq_dec ks k v)) k' 0 =
      assoc_default eq_nat_dec
                    (log_to_ks' l ks) k' 0.
  Proof.
    induction l; intros; simpl in *; auto using assoc_default_assoc_set_diff.
    repeat break_match; simpl in *; eauto.
    - do_bool. destruct (eq_nat_dec (eClient a) k); subst; simpl in *.
      + rewrite assoc_set_assoc_set_same. auto.
      + erewrite assoc_default_a_equiv; [|apply log_to_ks'_a_equiv;
                                           apply assoc_set_assoc_set_diff]; eauto.
    - do_bool. destruct (eq_nat_dec (eClient a) k); subst; simpl in *.
      + rewrite assoc_set_assoc_set_same. auto.
      + rewrite assoc_default_assoc_set_diff in *; auto; omega.
    - do_bool. destruct (eq_nat_dec (eClient a) k); subst; simpl in *.
      + erewrite <- assoc_set_assoc_set_same; eauto.
      + rewrite assoc_default_assoc_set_diff in *; auto; omega.
  Qed.

  Lemma a_equiv_refl :
    forall K V K_eq_dec (l : list (K * V)),
      a_equiv K_eq_dec l l.
  Proof.
    intros. unfold a_equiv. auto.
  Qed.

  Lemma a_equiv_sym :
    forall K V K_eq_dec (l : list (K * V)) l',
      a_equiv K_eq_dec l l' ->
      a_equiv K_eq_dec l' l.
  Proof.
    unfold a_equiv. intros. auto.
  Qed.
  
  Lemma a_equiv_trans :
    forall K V K_eq_dec (l : list (K * V)) l' l'',
      a_equiv K_eq_dec l l' ->
      a_equiv K_eq_dec l' l'' ->
      a_equiv K_eq_dec l l''.
  Proof.
    unfold a_equiv in *.
    intros. repeat find_higher_order_rewrite.
    auto.
  Qed.

  Lemma assoc_set_log_to_ks'_le:
    forall (l : list entry) (ks : list (nat * nat)) c i,
      assoc_default eq_nat_dec (log_to_ks' l ks) c 0 <= i ->
      a_equiv eq_nat_dec
              (assoc_set Nat.eq_dec (log_to_ks' l ks) c i)
              (log_to_ks' l (assoc_set Nat.eq_dec ks c i)).
  Proof.
    induction l; intros; simpl in *; eauto using a_equiv_refl.
    repeat break_if; simpl in *; eauto.
    - do_bool.
      destruct (eq_nat_dec (eClient a) c); subst.
      + repeat rewrite assoc_set_assoc_set_same.
        find_rewrite_lem assoc_default_assoc_set.
        assert (i = eId a) by (eapply le_antisym; auto;
                               eapply le_trans; [|eauto];
                               eauto using log_to_ks'_assoc_default_ks).
        subst. find_apply_hyp_hyp.
        find_rewrite_lem assoc_set_assoc_set_same.
        auto.
      + eapply a_equiv_sym.
        eapply a_equiv_trans;
          [eapply log_to_ks'_a_equiv;
            eapply assoc_set_assoc_set_diff; auto|].
        eapply a_equiv_sym. eauto.
    - do_bool.
      destruct (eq_nat_dec (eClient a) c); subst.
      + find_rewrite_lem assoc_default_assoc_set.
        find_apply_hyp_hyp.
        find_rewrite_lem assoc_set_assoc_set_same.
        auto.
      + rewrite assoc_default_assoc_set_diff in *; auto.
        omega.
    - do_bool.
      destruct (eq_nat_dec (eClient a) c); subst.
      + find_rewrite_lem assoc_default_assoc_set.
        rewrite assoc_set_assoc_set_same. 
        assert (i = eId a); subst; eauto.
        eapply le_antisym; eauto.
        eapply le_trans; [|eauto].
        eapply le_trans; [|eapply log_to_ks'_assoc_default_assoc_default_le].
        omega.
      + rewrite assoc_default_assoc_set_diff in *; auto. omega.
  Qed.

  Lemma log_to_ks'_assoc_default_lt :
    forall l ks c i,
      i < assoc_default Nat.eq_dec (log_to_ks' l (assoc_set Nat.eq_dec ks c i)) c 0 ->
      assoc_default Nat.eq_dec (log_to_ks' l (assoc_set Nat.eq_dec ks c i)) c 0 =
      assoc_default Nat.eq_dec (log_to_ks' l ks) c 0.
  Proof.
    induction l; intros; simpl in *.
    - rewrite assoc_default_assoc_set in *. omega.
    - repeat break_if; simpl in *; auto.
      + destruct (eq_nat_dec (eClient a) c); subst.
        * rewrite assoc_set_assoc_set_same; auto.
        * match goal with
            | [ |- context [ assoc_default ?eq (_ ?l (assoc_set ?eq (assoc_set ?eq ?ks ?c ?i)
                                                     ?c' ?i')) ?c 0 ] ] =>
              assert (assoc_default eq (log_to_ks' l (assoc_set eq (assoc_set eq ks c i) c' i')) c 0
                      = assoc_default eq (log_to_ks' l (assoc_set eq (assoc_set eq ks c' i') c i)) c 0)
                     by (apply assoc_default_a_equiv; apply log_to_ks'_a_equiv;
                         apply assoc_set_assoc_set_diff; auto)
          end.
          repeat find_rewrite. eauto.
      + destruct (eq_nat_dec (eClient a) c); subst.
        * do_bool.
          rewrite assoc_set_assoc_set_same in *.
          rewrite assoc_default_assoc_set in *.
  Admitted.
          
  Lemma log_to_ks'_assoc_set_le:
    forall (l : list entry) (ks : list (nat * nat)) c i,
      assoc_default eq_nat_dec ks c 0 <= i ->
      i < assoc_default eq_nat_dec (log_to_ks' l ks) c 0 ->
      a_equiv Nat.eq_dec (log_to_ks' l ks)
              (log_to_ks' l (assoc_set Nat.eq_dec ks c i)).
  Proof.
    induction l; intros; simpl in *; try omega.
    repeat break_if; simpl in *; eauto.
    - destruct (eq_nat_dec (eClient a) c); subst.
      + rewrite assoc_set_assoc_set_same. eauto using a_equiv_refl.
      + do_bool.
        eapply a_equiv_trans;
        [eapply IHl with (i := i); eauto;
         rewrite assoc_default_assoc_set_diff; auto|].
        apply log_to_ks'_a_equiv.
        eauto using assoc_set_assoc_set_diff.
    - do_bool.
      destruct (eq_nat_dec (eClient a) c); subst.
      + rewrite assoc_default_assoc_set in *.
        match goal with
          | [ _ : ?i < ?x, _ : eId ?e < ?i |- context [assoc_set ?eq ?ks ?c (eId ?e) ]] =>
            assert (x = (assoc_default eq (assoc_set eq ks c (eId e)) c 0))
        end. eapply log_to_ks'_assoc_default_eq.
  Admitted.

  Lemma log_to_ks'_rev :
    forall l ks,
      a_equiv eq_nat_dec (log_to_ks' (rev l) ks)
              (log_to_ks' l ks).
  Proof.
    induction l; intros; simpl in *; auto using a_equiv_refl.
    break_if; simpl in *;
    rewrite log_to_ks'_app; simpl in *; auto.
    - break_if; simpl in *; eauto.
      + do_bool.
        eapply a_equiv_trans; eauto using assoc_set_log_to_ks'_le.
      + do_bool.
        match goal with
          | [ H : _ < _ |- _ ] => 
            erewrite assoc_default_a_equiv in H
        end; eauto.

        eapply a_equiv_trans; eauto using assoc_set_log_to_ks'_le.
        (*
        find_apply_lem_hyp a_equiv_sym.
        eapply a_equiv_trans; [|eauto].
        apply assoc_set_log_to_ks'_le.
         *)
  Admitted.

  
  Lemma client_cache_keys_correct_clientCache_complete :
    forall net,
      client_cache_keys_correct net ->
      client_cache_complete net.
  Proof.
    unfold client_cache_keys_correct, client_cache_complete.
    intros.
    match goal with
      | _ : context[removeAfterIndex ?l ?i] |- _ =>
        induction (removeAfterIndex l i) eqn:?
    end; simpl in *; intuition.
    subst.
  Admitted.

  Lemma state_machine_do_generic_server :
    raft_net_invariant_do_generic_server state_machine_log.
  Proof.
    red. unfold state_machine_log in *. simpl in *. intros.
    find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    unfold doGenericServer in *. break_let.
    find_inversion. simpl in *.
    find_copy_apply_lem_hyp applyEntries_execute_log'. repeat find_rewrite.
    find_copy_apply_lem_hyp applyEntries_lastApplied_commitIndex_log.
    break_and. repeat find_rewrite.
    simpl in *. repeat find_higher_order_rewrite.
    break_if; do_bool.
    - rewrite filter_and by
          (intros;
           match goal with
             | |- context [?x <? ?y] =>
               destruct (x <? y) eqn:?; auto
           end; do_bool;
           find_eapply_lem_hyp findGtIndex_necessary; omega).
      find_copy_apply_lem_hyp logs_sorted_invariant; unfold logs_sorted in *; intuition.
      match goal with
        | |- context [commitIndex ?st] =>
          rewrite removeAfterIndex_app
          with (i := commitIndex st)
                 (i' := lastApplied st); intuition eauto
      end.
      rewrite rev_app_distr.
      unfold deduplicate_log.
      rewrite deduplicate_log'_app.
      unfold execute_log.
      rewrite execute_log'_app. break_let.
      simpl in *.
      rewrite client_cache_keys_correct_invariant; auto.
      eauto using snd_execute_log'.
    - match goal with
        | |- context [filter ?f ?l] =>
          assert (filter f l = filter (fun _ => false) l) by
              (apply filter_fun_ext_eq;
               intros; do_bool; right;
               apply leb_correct_conv;
               eapply le_lt_trans; eauto;
               eapply findGtIndex_necessary; eauto)
      end.
      repeat find_rewrite.
      rewrite filter_false. reflexivity.
  Qed.

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
