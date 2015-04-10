Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.
Require Import Sorting.Permutation.


Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import Raft.
Require Import CommonTheorems.
Require Import TraceUtil.
Require Import Linearizability.
Require Import OutputImpliesAppliedInterface.
Require Import UniqueIndicesInterface.
Require Import AppliedImpliesInputInterface.
Require Import CausalOrderPreservedInterface.
Require Import OutputCorrectInterface.
Require Import InputBeforeOutputInterface.

Section RaftLinearizableProofs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.
  Context {aiii : applied_implies_input_interface}.
  Context {copi : causal_order_preserved_interface}.
  Context {iboi : input_before_output_interface}.
  Context {oci : output_correct_interface}.


  Definition op_eq_dec : forall x y : op key, {x = y} + {x <> y}.
  Proof.
    decide equality; auto using key_eq_dec.
  Qed.


  Fixpoint import (tr : list (name * (raft_input + list raft_output)))
  : list (op key) :=
    match tr with
      | [] => []
      | (_, (inl (ClientRequest c id cmd))) :: xs =>
        I (c, id) :: remove op_eq_dec (I (c, id)) (import xs)
      | (_, (inr l)) :: xs =>
        let os := dedup op_eq_dec
                        (filterMap (fun x =>
                               match x with
                                 | ClientResponse c id cmd => Some (O (c, id))
                                 | _ => None
                               end) l)
        in os ++ remove_all op_eq_dec os (import xs)
      | _ :: xs => import xs
    end.

  Inductive exported (env_i : key -> option input) (env_o : key -> option output) :
    list (IR key) -> list (input * output) -> Prop :=
  | exported_nil : exported env_i env_o nil nil
  | exported_IO : forall k i o l tr,
                    env_i k = Some i ->
                    env_o k = Some o ->
                    exported env_i env_o l tr ->
                    exported env_i env_o (IRI k :: IRO k :: l) ((i, o) :: tr)
  | exported_IU : forall k i o l tr,
                    env_i k = Some i ->
                    exported env_i env_o l tr ->
                    exported env_i env_o (IRI k :: IRU k :: l) ((i, o) :: tr).

  Require Import Sumbool.
  Require Import Arith.

  Fixpoint get_input (tr : list (name * (raft_input + list raft_output))) (k : key)
    : option input :=
    match tr with
      | [] => None
      | (_, (inl (ClientRequest c id cmd))) :: xs =>
        if (sumbool_and _ _ _ _
                        (eq_nat_dec c (fst k))
                        (eq_nat_dec id (snd k))) then
          Some cmd
        else
          get_input xs k
      | _ :: xs => get_input xs k
    end.

  Fixpoint get_output' (os : list raft_output) (k : key) : option output :=
    match os with
      | [] => None
      | ClientResponse c id o :: xs =>
        if (sumbool_and _ _ _ _
                        (eq_nat_dec c (fst k))
                        (eq_nat_dec id (snd k))) then
          Some o
        else
          get_output' xs k
      | _ :: xs => get_output' xs k
    end.

  Fixpoint get_output (tr : list (name * (raft_input + list raft_output))) (k : key)
    : option output :=
    match tr with
      | [] => None
      | (_, (inr os)) :: xs => (match get_output' os k with
                                 | Some o => Some o
                                 | None => get_output xs k
                               end)
      | _ :: xs => get_output xs k
    end.

  Lemma deduplicate_log_In :
    forall l e,
      In e l ->
      exists e',
        eClient e' = eClient e /\
        eId e' = eId e /\
        In e' (deduplicate_log l).
  Proof.
    (* this is now false *)
  Admitted.

  Lemma deduplicate_log_In_if :
    forall l e,
      In e (deduplicate_log l) ->
      In e l.
  Admitted.

  Fixpoint log_to_IR (env_o : key -> option output) (log : list entry) {struct log} : list (IR key) :=
    match log with
      | [] => []
      | mkEntry h client id index term input :: log' =>
        (match env_o (client, id) with
           | None => [IRI (client, id); IRU (client, id)]
           | Some _ => [IRI (client, id); IRO (client, id)]
         end) ++ log_to_IR env_o log'
    end.

  Lemma log_to_IR_good_trace :
    forall env_o log,
      good_trace _ (log_to_IR env_o log).
  Proof.
    intros.
    induction log; simpl in *; auto.
    - repeat break_match; simpl in *; constructor; auto.
  Qed.


  Lemma in_import_in_trace_O :
    forall tr k,
      In (O k) (import tr) ->
      exists os h,
        In (h, inr os) tr /\
        exists o, In (ClientResponse (fst k) (snd k) o) os.
  Proof.
    induction tr; intros; simpl in *; intuition.
    repeat break_match; subst; intuition.
    - find_apply_hyp_hyp. break_exists_exists.
      intuition.
    - simpl in *. intuition; try congruence.
      find_apply_lem_hyp in_remove.
      find_apply_hyp_hyp. break_exists_exists.
      intuition.
    - do_in_app. intuition.
      + find_apply_lem_hyp in_dedup_was_in.
        find_apply_lem_hyp In_filterMap.
        break_exists. intuition.
        break_match; try congruence.
        find_inversion.
        repeat eexists; intuition eauto.
      + find_apply_lem_hyp in_remove_all_was_in.
        find_apply_hyp_hyp. break_exists_exists.
        intuition.
  Qed.

  Lemma in_import_in_trace_I :
    forall tr k,
      In (I k) (import tr) ->
      exists h i,
        In (h, inl (ClientRequest (fst k) (snd k) i)) tr.
  Proof.
    induction tr; intros; simpl in *; intuition.
    repeat break_match; subst.
    - find_apply_hyp_hyp. break_exists.
      eauto 10.
    - simpl in *. intuition.
      + find_inversion. simpl. eauto 10.
      + find_apply_lem_hyp in_remove.
        find_apply_hyp_hyp. break_exists. eauto 10.
    - do_in_app. intuition.
      + find_apply_lem_hyp in_dedup_was_in.
        find_eapply_lem_hyp In_filterMap. break_exists. break_and.
        break_match; discriminate.
      + find_eapply_lem_hyp in_remove_all_was_in.
        find_apply_hyp_hyp. break_exists. eauto 10.
  Qed.

  Lemma in_applied_entries_in_IR :
    forall log e client id env,
      eClient e = client ->
      eId e = id ->
      In e log ->
      (exists o, env (client, id) = Some o) ->
      In (IRO (client, id)) (log_to_IR env log).
  Proof.
    intros.
    induction log; simpl in *; intuition.
    - subst. break_exists.
      repeat break_match; intuition.
      simpl in *.
      subst. congruence.
    - repeat break_match; in_crush.
  Qed.

  Theorem In_get_output' :
    forall l client id o,
      In (ClientResponse client id o) l ->
      exists o', get_output' l (client, id) = Some o'.
  Proof.
    intros. induction l; simpl in *; intuition.
    - subst. break_if; simpl in *; intuition eauto.
    - break_match; simpl in *; intuition eauto.
      break_if; simpl in *; intuition eauto.
  Qed.

  Theorem import_get_output :
    forall tr k,
      In (O k) (import tr) ->
      exists o,
        get_output tr k = Some o.
  Proof.
    intros.
    induction tr; simpl in *; intuition.
    repeat break_match; intuition; subst; simpl in *; intuition; try congruence;
    try do_in_app; intuition eauto.
    - find_apply_lem_hyp in_remove; auto.
    - find_apply_lem_hyp in_dedup_was_in; auto.
      find_apply_lem_hyp In_filterMap.
      break_exists; break_match; intuition; try congruence.
      subst. find_inversion.
      find_apply_lem_hyp In_get_output'. break_exists; congruence.
    - find_apply_lem_hyp in_remove_all_was_in. auto.
  Qed.

  Lemma IRO_in_IR_in_log :
    forall k log tr,
      In (IRO k) (log_to_IR (get_output tr) log) ->
      exists e out,
        eClient e = fst k /\
        eId e = snd k /\
        get_output tr k = Some out /\
        In e log.
  Proof.
    induction log; intros; simpl in *; intuition.
    repeat break_match; subst; simpl in *; intuition; try congruence; try find_inversion; simpl.
    - eexists. eexists. intuition; eauto.
    - find_apply_hyp_hyp. break_exists_exists. intuition.
    - find_apply_hyp_hyp. break_exists_exists. intuition.
  Qed.

  Lemma get_output'_In :
    forall l k out,
      get_output' l k = Some out ->
      In (ClientResponse (fst k) (snd k) out) l.
  Proof.
    induction l; intros; simpl in *; intuition.
    - discriminate.
    - repeat break_match; subst; eauto.
      find_inversion. break_and. subst. eauto.
  Qed.

  Lemma get_output_import_O :
    forall tr k out,
      get_output tr k = Some out ->
      In (O k) (import tr).
  Proof.
    induction tr; intros; simpl in *.
    - discriminate.
    - repeat break_match; subst; simpl; intuition eauto.
      + right. apply remove_preserve; try discriminate. eauto.
      + find_inversion. apply in_or_app. left.
        find_apply_lem_hyp get_output'_In.
        apply dedup_In.
        eapply filterMap_In; eauto.
        simpl. now rewrite <- surjective_pairing.
      + apply in_or_app. right.
        apply in_remove_all_preserve.
        * intro. find_apply_lem_hyp in_dedup_was_in.
          find_apply_lem_hyp In_filterMap.
          break_exists. break_and.
          break_match; try discriminate.
          find_inversion.
          find_apply_lem_hyp In_get_output'.
          break_exists. congruence.
        * eauto.
  Qed.

  Lemma IRU_in_IR_in_log :
    forall k log tr,
      In (IRU k) (log_to_IR (get_output tr) log) ->
      exists e,
        eClient e = fst k /\
        eId e = snd k /\
        get_output tr k = None /\
        In e log.
  Proof.

    induction log; intros; simpl in *; intuition.
    repeat break_match; subst; simpl in *; intuition; try congruence; try find_inversion; simpl.
    - find_apply_hyp_hyp. break_exists_exists. intuition.
    - eexists. intuition; eauto.
    - find_apply_hyp_hyp. break_exists_exists. intuition.
  Qed.

  Lemma trace_I_in_import :
    forall tr k h i,
      In (h, inl (ClientRequest (fst k) (snd k) i)) tr ->
      In (I k) (import tr).
  Proof.
    induction tr; intros; simpl in *; intuition; subst.
    - rewrite <- surjective_pairing. intuition.
    - break_match; simpl; eauto.
      subst.
      destruct (key_eq_dec (n, n0) k).
      + subst. auto.
      + right. apply remove_preserve.
        * congruence.
        * eauto.
    - apply in_or_app.
      right.
      apply in_remove_all_preserve.
      + intro. find_apply_lem_hyp in_dedup_was_in.
        find_apply_lem_hyp In_filterMap.
        break_exists. break_and.
        break_match; try discriminate.
      + eauto.
  Qed.

  Lemma get_IR_input_of_log_to_IR :
    forall env log,
      get_IR_input_keys _ (log_to_IR env log) =
      map (fun e => (eClient e, eId e)) log.
  Proof.
    induction log; simpl; intuition.
    repeat break_match; subst; simpl in *;
    rewrite get_IR_input_keys_defn; auto using f_equal.
  Qed.

  Lemma get_IR_output_of_log_to_IR :
    forall env log,
      get_IR_output_keys _ (log_to_IR env log) =
      map (fun e => (eClient e, eId e)) log.
  Proof.
    induction log; simpl; intuition.
    repeat break_match; subst; simpl in *;
    repeat rewrite get_IR_output_keys_defn; auto using f_equal.
  Qed.


  Lemma NoDup_input_import :
    forall tr,
      NoDup (get_op_input_keys key (import tr)).
  Proof.
    induction tr; intros.
    - constructor.
    - simpl. repeat break_match; subst.
      + auto.
      + rewrite get_op_input_keys_defn. constructor; auto.
        * intro. find_apply_lem_hyp get_op_input_keys_sound.
          eapply remove_In; eauto.
        * eapply subseq_NoDup; eauto.
          eapply subseq_get_op_input_keys.
          auto using subseq_remove.
      + rewrite get_op_input_keys_app.
        rewrite get_op_input_keys_on_Os_nil.
        * simpl.
          eapply subseq_NoDup; eauto.
          eapply subseq_get_op_input_keys.
          apply subseq_remove_all.
          apply subseq_refl.
        * intros.
          find_apply_lem_hyp in_dedup_was_in.
          find_apply_lem_hyp In_filterMap.
          break_exists.  break_and.
          break_match; try discriminate.
          subst. find_inversion. eauto.
  Qed.

  Lemma NoDup_output_import :
    forall tr,
      NoDup (get_op_output_keys key (import tr)).
  Proof.
    induction tr; intros.
    - constructor.
    - simpl. repeat break_match; subst.
      + auto.
      + rewrite get_op_output_keys_defn.
        eapply subseq_NoDup; eauto.
        apply subseq_get_op_output_keys.
        apply subseq_remove.
      + rewrite get_op_output_keys_app.
        apply NoDup_disjoint_append.
        * apply get_op_output_keys_preserves_NoDup.
          apply NoDup_dedup.
        * eapply subseq_NoDup; eauto.
          eapply subseq_get_op_output_keys.
          apply subseq_remove_all.
          apply subseq_refl.
        * intros. intro.
          repeat find_apply_lem_hyp get_op_output_keys_sound.
          eapply in_remove_all_not_in; eauto.
  Qed.

  Lemma before_import_output_before_input :
    forall k k' tr,
      before (O k) (I k') (import tr) ->
      output_before_input (fst k) (snd k) (fst k') (snd k') tr.
  Proof.
    induction tr; intros; simpl in *; intuition.
    repeat break_match; subst; simpl in *; intuition eauto; try congruence;
    unfold output_before_input; simpl in *; intuition.
    - right. intuition.
      + do_bool.
        destruct k'.  simpl in *.
        match goal with
          | _ : I (?x, ?y) = I (?x', ?y') -> False |- _ =>
            destruct (eq_nat_dec x x'); destruct (eq_nat_dec y y')
        end; subst; intuition.
        * right. do_bool. intuition.
        * left. do_bool. intuition.
        * left. do_bool. intuition.
      + apply IHtr. eauto using before_remove.
    - break_if; intuition. right.
      intuition. find_apply_lem_hyp before_app; [find_apply_lem_hyp before_remove_all|]; intuition eauto.
      + find_apply_lem_hyp in_dedup_was_in.
        find_apply_lem_hyp In_filterMap.
        break_exists. intuition. break_match; congruence.
      + find_apply_lem_hyp in_dedup_was_in.
        find_apply_lem_hyp In_filterMap.
        break_exists.
        intuition. break_match; try congruence.
        subst. find_inversion. simpl in *.
        match goal with
          | H : _ -> False |- False => apply H
        end. eexists; eauto.
  Qed.

  Lemma has_key_true_key_of :
    forall c i e,
      has_key c i e = true ->
      key_of e = (c, i).
  Proof.
    intros. unfold has_key, key_of in *.
    break_match. subst. simpl in *. repeat (do_bool; intuition).
  Qed.

  Lemma key_of_has_key_true :
    forall c i e,
      key_of e = (c, i) ->
      has_key c i e = true.
  Proof.
    intros. unfold has_key, key_of in *.
    break_match. subst. simpl in *. find_inversion. repeat (do_bool; intuition).
  Qed.

  Lemma has_key_false_key_of :
    forall c i e,
      has_key c i e = false ->
      key_of e <> (c, i).
  Proof.
    intros. unfold has_key, key_of in *.
    break_match. subst. simpl in *. repeat (do_bool; intuition); congruence.
  Qed.

  Lemma key_of_has_key_false :
    forall c i e,
      key_of e <> (c, i) ->
      has_key c i e = false.
  Proof.
    intros. unfold has_key, key_of in *.
    break_match. subst. simpl in *. repeat (do_bool; intuition).
    match goal with
      | _ : (?x, ?y) = (?x', ?y') -> False |- _ =>
        destruct (eq_nat_dec x x'); destruct (eq_nat_dec y y')
    end; subst; intuition.
    - right. do_bool. congruence.
    - left. do_bool. congruence.
    - left. do_bool. congruence.
  Qed.

  Lemma before_func_deduplicate :
    forall k k' l,
      before_func (has_key (fst k) (snd k)) (has_key (fst k') (snd k')) l ->
      before_func (has_key (fst k) (snd k)) (has_key (fst k') (snd k')) (deduplicate_log l).
  Admitted.

  Lemma entries_ordered_before_log_to_IR :
    forall k k' net tr,
      In (O k) (import tr) ->
      k <> k' ->
      entries_ordered (fst k) (snd k) (fst k') (snd k') net ->
      before (IRO k) (IRI k')
             (log_to_IR (get_output tr) (deduplicate_log (applied_entries (nwState net)))).
  Proof.
    intros. unfold entries_ordered in *.
    remember (applied_entries (nwState net)) as l; clear Heql.
    find_apply_lem_hyp before_func_deduplicate.
    remember (deduplicate_log l) as l'; clear Heql'. clear l. rename l' into l.
    induction l; simpl in *; intuition.
    - repeat break_match; subst; simpl in *; repeat (do_bool; intuition).
      + destruct k; simpl in *; subst. right. intuition.
        find_inversion. simpl in *. intuition.
      + exfalso. destruct k; subst; simpl in *.
        find_apply_lem_hyp import_get_output. break_exists. congruence.
    - repeat break_match; subst; simpl in *; repeat (do_bool; intuition).
      + right. destruct k'. simpl in *. intuition; try congruence.
        destruct (key_eq_dec k (eClient, eId)); subst; intuition.
        right. intuition; congruence.
      + right. destruct k'. simpl in *. intuition; try congruence.
        destruct (key_eq_dec k (eClient, eId)); subst; intuition.
        right. intuition; congruence.
      + right. intuition; [find_inversion; simpl in *; intuition|].
        right. intuition. congruence.
      + right. intuition; [find_inversion; simpl in *; intuition|].
        right. intuition. congruence.
  Qed.

  Lemma input_before_output_import :
    forall tr k,
      before_func (is_input_with_key (fst k) (snd k))
                  (is_output_with_key (fst k) (snd k)) tr ->
      before (I k) (O k) (import tr).
  Proof.
    intros; induction tr; simpl in *; intuition.
    - repeat break_match; subst; simpl in *; intuition; try congruence.
      repeat (do_bool; intuition).
      destruct k; subst; simpl in *; intuition.
    - repeat break_match; subst; simpl in *; intuition; try congruence.
      + destruct k.
        match goal with
          | |- context [ I (?x, ?y) = I (?x', ?y') ] =>
            destruct (op_eq_dec (I (x, y)) (I (x', y')))
        end; subst; intuition.
        right.
        intuition; try congruence.
        apply before_remove_if; intuition.
      + break_if; try congruence.
        apply before_app_if; [apply before_remove_all_if|]; auto.
        * intuition. find_apply_lem_hyp in_dedup_was_in.
          find_apply_lem_hyp In_filterMap. break_exists.
          break_match; intuition; congruence.
        * intuition.
          match goal with
            | H : _ -> False |- False => apply H
          end.
          find_apply_lem_hyp in_dedup_was_in.
          find_apply_lem_hyp In_filterMap.
          break_exists. intuition. break_match; try congruence.
          find_inversion.
          unfold key_in_output_list. simpl.
          eexists; eauto.
  Qed.

  Lemma I_before_O :
    forall failed net tr k,
      step_f_star step_f_init (failed, net) tr ->
      In (O k) (import tr) ->
      before (I k) (O k) (import tr).
  Proof.
    intros.
    find_apply_lem_hyp in_import_in_trace_O.
    find_eapply_lem_hyp output_implies_input_before_output; eauto.
    eauto using input_before_output_import.
  Qed.

  Lemma get_IR_input_keys_log_to_IR :
    forall l env_o,
      get_IR_input_keys key (log_to_IR env_o l) =
      map (fun e => (eClient e, eId e)) l.
  Proof.
    intros. induction l; simpl in *; intuition.
    repeat break_match; subst; compute; simpl; f_equal; auto.
  Qed.

  Lemma get_IR_output_keys_log_to_IR :
    forall l env_o,
      get_IR_output_keys key (log_to_IR env_o l) =
      map (fun e => (eClient e, eId e)) l.
  Proof.
    intros. induction l; simpl in *; intuition.
    repeat break_match; subst; compute; simpl; f_equal; auto.
  Qed.


  Lemma deduplicate_log'_filter :
    forall l k ks,
      deduplicate_log' l (k :: ks) =
      filter (fun e => negb (andb (beq_nat (eClient e) (fst k))
                                 (beq_nat (eId e) (snd k)))) (deduplicate_log' l ks).
  Admitted.

  Lemma deduplicate_log'_In_elim :
    forall x l k ks,
      In x (deduplicate_log' l (k :: ks)) ->
      In x (deduplicate_log' l ks) /\ key_of x <> k.
  Admitted.

  Lemma NoDup_input_log :
    forall l env_o,
      NoDup (get_IR_input_keys key (log_to_IR env_o (deduplicate_log l))).
  Proof.
    intros.
    rewrite get_IR_input_keys_log_to_IR.
    induction l; simpl in *; constructor.
    - intuition.
      do_in_map.
      find_apply_lem_hyp deduplicate_log'_In_elim.
      unfold key_of in *. intuition.
    - rewrite deduplicate_log'_filter.
      eauto using NoDup_map_filter.
  Qed.

  Lemma NoDup_output_log :
    forall l env_o,
      NoDup (get_IR_output_keys key (log_to_IR env_o (deduplicate_log l))).
  Proof.
    intros.
    rewrite get_IR_output_keys_log_to_IR.
    induction l; simpl in *; constructor.
    - intuition.
      do_in_map.
      find_apply_lem_hyp deduplicate_log'_In_elim.
      unfold key_of in *. intuition.
    - rewrite deduplicate_log'_filter.
      eauto using NoDup_map_filter.
  Qed.

  Hint Constructors exported.

  Lemma exported_snoc_IO :
    forall env_i env_o ir tr i o k,
      exported env_i env_o ir tr ->
      env_i k = Some i ->
      env_o k = Some o ->
      exported env_i env_o (ir ++ [IRI k; IRO k]) (tr ++ [(i, o)]).
  Proof.
    induction 1; intros; simpl; auto.
  Qed.

  Lemma exported_snoc_IU :
    forall env_i env_o ir tr i k o,
      exported env_i env_o ir tr ->
      env_i k = Some i ->
      env_o k = None ->
      exported env_i env_o (ir ++ [IRI k; IRU k]) (tr ++ [(i, o)]).
  Proof.
    induction 1; intros; simpl; auto.
  Qed.

  Lemma execute_log'_app :
    forall xs ys st tr,
      execute_log' (xs ++ ys) st tr =
      let (tr', st') := execute_log' xs st tr in
      execute_log' ys st' tr'.
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. repeat break_let.
      rewrite IHxs. break_let. find_inversion. auto.
  Qed.

  Lemma log_to_IR_app :
    forall xs ys env,
      log_to_IR env (xs ++ ys) = log_to_IR env xs ++ log_to_IR env ys.
  Proof.
    induction xs; intros; simpl; intuition.
    repeat break_match; subst; simpl; auto using f_equal.
  Qed.

  Lemma exported_execute_log' :
    forall env_i env_o l es tr st,
      (forall e, In e l -> env_i (eClient e, eId e) = Some (eInput e)) ->
      (forall xs ys e tr' st' o o0 st'',
         l = xs ++ e :: ys ->
         execute_log' xs st tr = (tr', st') ->
         handler (eInput e) st' = (o, st'') ->
         env_o (eClient e, eId e) = Some o0 ->
         o = o0) ->
      execute_log es = (tr, st) ->
      exported env_i env_o (log_to_IR env_o es) tr ->
      exported env_i env_o (log_to_IR env_o (es ++ l)) (fst (execute_log' l st tr)).
  Proof.
    induction l using rev_ind; intros; simpl in *.
    - rewrite app_nil_r.  auto.
    - rewrite execute_log'_app. simpl. repeat break_let.
      simpl.
      eapply_prop_hyp execute_log execute_log; auto.
      + find_rewrite. simpl in *.
        rewrite <- app_ass.
        rewrite log_to_IR_app.
        simpl.
        specialize (H x). concludes.
        specialize (H0 l [] x l0 d).
        break_match; subst; simpl in *.
        rewrite app_nil_r.
        break_match.
        * specialize (H0 o o0 d0). repeat concludes.
          apply exported_snoc_IO; congruence.
        * apply exported_snoc_IU; auto.
      + intros. apply H. intuition.
      + intros. subst. eapply H0 with (ys0 := ys ++ [x]).
        rewrite app_ass. simpl. eauto.
        eauto.
        eauto.
        eauto.
  Qed.

  Lemma exported_execute_log :
    forall env_i env_o l,
      (forall e, In e l -> env_i (eClient e, eId e) = Some (eInput e)) ->
      (forall xs ys e tr' st' o o0 st'',
         l = xs ++ e :: ys ->
         execute_log xs  = (tr', st') ->
         handler (eInput e) st' = (o, st'') ->
         env_o (eClient e, eId e) = Some o0 ->
         o = o0) ->
      exported env_i env_o (log_to_IR env_o l) (fst (execute_log l)).
  Proof.
    intros.
    unfold execute_log.
    change (log_to_IR env_o l) with (log_to_IR env_o ([] ++ l)).
    eapply exported_execute_log'; eauto.
  Qed.

  Definition input_correct (tr : list (name * (raft_input + list raft_output))) : Prop :=
    (forall client id i i' h h',
       In (h, inl (ClientRequest client id i)) tr ->
       In (h', inl (ClientRequest client id i')) tr ->
       i = i').

  Lemma in_input_trace_get_input :
    forall tr e,
      input_correct tr ->
      in_input_trace (eClient e) (eId e) (eInput e) tr ->
      get_input tr (eClient e, eId e) = Some (eInput e).
  Proof.
    unfold in_input_trace, input_correct.
    induction tr; intros; break_exists; simpl in *; intuition; subst;
    repeat break_match; intuition; subst; eauto 10 using f_equal.
  Qed.

  Lemma get_output_in_output_trace :
    forall tr client id o,
      get_output tr (client, id) = Some o ->
      in_output_trace client id o tr.
  Proof.
    intros. induction tr; simpl in *; try congruence.
    repeat break_let. subst.
    repeat break_match; simpl in *; intuition; subst;
    try solve [unfold in_output_trace in *;break_exists_exists; intuition].
    find_inversion. find_apply_lem_hyp get_output'_In.
    repeat eexists; eauto; in_crush.
  Qed.

  Lemma deduplicate_partition :
    forall l ks xs e ys xs' e' ys',
      deduplicate_log' l ks = xs ++ e :: ys ->
      deduplicate_log' l ks = xs' ++ e' :: ys' ->
      eClient e = eClient e' ->
      eId e = eId e' ->
      xs = xs'.
  Admitted.

  Lemma applied_entries_applied_implies_input_state :
    forall net e,
      In e (applied_entries (nwState net)) ->
      applied_implies_input_state (eClient e) (eId e) (eInput e) net.
  Proof.
    intros.
    red. exists e.
    intuition.
    - red. auto.
    - unfold applied_entries in *. break_match.
      + find_apply_lem_hyp in_rev.
        find_apply_lem_hyp removeAfterIndex_in.
        eauto.
      + simpl in *. intuition.
  Qed.

  Theorem raft_linearizable' :
    forall failed net tr,
      input_correct tr ->
      step_f_star step_f_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof.
    intros.
    exists (log_to_IR (get_output tr) (deduplicate_log (applied_entries (nwState net)))).
    exists (fst (execute_log (deduplicate_log (applied_entries (nwState net))))).
    exists (snd (execute_log (deduplicate_log (applied_entries (nwState net))))).
    intuition eauto using execute_log_correct.
    - eapply equivalent_intro; eauto using log_to_IR_good_trace, key_eq_dec.
      + (* In O -> In IRO *)
        intros.
        find_copy_apply_lem_hyp in_import_in_trace_O.
        find_eapply_lem_hyp output_implies_applied; eauto.
        unfold in_applied_entries in *.
        break_exists. intuition.
        destruct k; simpl in *.
        find_apply_lem_hyp deduplicate_log_In.
        break_exists. intuition.
        repeat find_rewrite.
        eapply in_applied_entries_in_IR; eauto.
        apply import_get_output. auto.
      + (* In IRO -> In O *)
        intros.
        find_apply_lem_hyp IRO_in_IR_in_log. break_exists. break_and.
        eapply get_output_import_O; eauto.
      + (* In IRU -> In I *)
        intros.
        find_apply_lem_hyp IRU_in_IR_in_log. break_exists. break_and.
        destruct k as [c id].
        find_apply_lem_hyp deduplicate_log_In_if.
        find_eapply_lem_hyp applied_implies_input; eauto.
        * unfold in_input_trace in *. break_exists.
          eauto using trace_I_in_import.
        * simpl in *. subst.
          auto using applied_entries_applied_implies_input_state.
      + (* before preserved *)
        intros.
        assert (k <> k').
        * intuition. subst.
          find_copy_apply_lem_hyp before_In.
          find_eapply_lem_hyp I_before_O; eauto.
          find_eapply_lem_hyp before_antisymmetric; auto.
          congruence.
        * eauto using before_In, before_import_output_before_input, causal_order_preserved,
          entries_ordered_before_log_to_IR.
      + (* I before O *)
        intros. eauto using I_before_O.
      + (* In IRU -> not In O *)
        intros.
        find_apply_lem_hyp IRU_in_IR_in_log. break_exists. break_and.
        intro.
        find_apply_lem_hyp import_get_output.
        break_exists. congruence.
      + (* NoDup op input *)
        apply NoDup_input_import.
      + (* NoDup IR input *)
        apply NoDup_input_log.
      + (* NoDup op output *)
        apply NoDup_output_import.
      + (* NoDup IR output *)
        apply NoDup_output_log.
    - apply exported_execute_log.
      + intros.
        find_apply_lem_hyp deduplicate_log_In_if.
        apply in_input_trace_get_input.
        * auto.
        * eapply applied_implies_input; eauto.
          auto using applied_entries_applied_implies_input_state.
      + intros.
        find_apply_lem_hyp get_output_in_output_trace.
        find_eapply_lem_hyp output_correct_invariant; eauto.
        unfold output_correct in *.
        break_exists. intuition.
        find_eapply_lem_hyp deduplicate_partition; eauto.
        subst.
        repeat find_rewrite.
        find_apply_lem_hyp app_inv_head. find_inversion.
        unfold execute_log in *.
        rewrite execute_log'_app in *. simpl in *.
        repeat break_let. repeat find_inversion.
        rewrite rev_app_distr in *. simpl in *.
        unfold value in *. find_inversion.
        repeat find_rewrite. find_inversion. auto.
  Qed.
End RaftLinearizableProofs.
