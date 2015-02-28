Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import Raft.
Require Import CommonTheorems.
Require Import Linearizability.
Require Import RaftLinearizableDefinitions.
Require Import OutputImpliesAppliedInterface.
Require Import UniqueIndicesInterface.
Require Import AppliedImpliesInputInterface.

Section RaftLinearizableProofs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.
  Context {aiii : applied_implies_input_interface}.

  Definition key : Type := nat * nat.

  Definition key_eq_dec : forall x y : key, {x = y} + {x <> y}.
  Proof.
    decide equality; auto using eq_nat_dec.
  Qed.

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

  Fixpoint log_to_IR (env_o : key -> option output) (log : list entry) : list (IR key) :=
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

  Fixpoint execute_log' (log : list entry) (st : data) (l : list (input * output))
  : (list (input * output) * data) :=
    match log with
      | [] => (l, st)
      | e :: log' => let '(o, st') := handler (eInput e) st in
                    execute_log' log' st' (l ++ [(eInput e, o)])
    end.

  Definition execute_log (log : list entry) : (list (input * output) * data) :=
    execute_log' log init [].



  Lemma fst_execute_log' :
    forall log st tr,
      fst (execute_log' log st tr) = tr ++ fst (execute_log' log st []).
  Proof.
    induction log; intros.
    - simpl. rewrite app_nil_r. auto.
    - simpl. break_let. rewrite IHlog. rewrite app_ass. simpl.
      rewrite IHlog with (tr := [(eInput a, o)]).
      auto.
  Qed.

  Lemma snd_execute_log' :
    forall log st tr,
      snd (execute_log' log st tr) = snd (execute_log' log st []).
  Proof.
    induction log; intros.
    - auto.
    - simpl. break_let. rewrite IHlog.
      rewrite IHlog with (tr := [(eInput a, o)]).
      auto.
  Qed.

  Lemma execute_log_correct' :
    forall log st,
      step_1_star st (snd (execute_log' log st []))
                  (fst (execute_log' log st [])).
  Proof.
    induction log; intros.
    - simpl. constructor.
    - simpl. break_let.
      rewrite fst_execute_log'.
      rewrite snd_execute_log'.
      unfold step_1_star in *.
      econstructor.
      + constructor. eauto.
      + auto.
  Qed.

  Lemma execute_log_correct :
    forall log,
      step_1_star init (snd (execute_log log))
                  (fst (execute_log log)).
  Proof.
    intros. apply execute_log_correct'.
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
        apply NoDup_disjoint_append.
        * apply get_op_input_keys_preserves_NoDup.
          apply NoDup_dedup.
        * eapply subseq_NoDup; eauto.
          eapply subseq_get_op_input_keys.
          apply subseq_remove_all.
          apply subseq_refl.
        * intros. intro.
          repeat find_apply_lem_hyp get_op_input_keys_sound.
          eapply in_remove_all_not_in; eauto.
  Qed.

  Theorem raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_f_star step_f_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof.
    intros.
    exists (log_to_IR (get_output tr) (applied_entries (nwState net))).
    exists (fst (execute_log (applied_entries (nwState net)))).
    exists (snd (execute_log (applied_entries (nwState net)))).
    intuition eauto using execute_log_correct.
    - eapply equivalent_intro; eauto using log_to_IR_good_trace, key_eq_dec.
      + (* In O -> In IRO *)
        intros.
        find_copy_apply_lem_hyp in_import_in_trace_O.
        find_eapply_lem_hyp output_implies_applied; eauto.
        unfold in_applied_entries in *.
        break_exists. intuition.
        destruct k; simpl in *.
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
        find_eapply_lem_hyp applied_implies_input; eauto.
        unfold in_input in *. break_exists. break_and.
        eauto using trace_I_in_import.
      + (* before preserved *)
        admit.
      + (* I before O *)
        admit.
      + (* In IRU -> not In O *)
        intros.
        find_apply_lem_hyp IRU_in_IR_in_log. break_exists. break_and.
        intro.
        find_apply_lem_hyp import_get_output.
        break_exists. congruence.
      + (* NoDup op input *)
        apply NoDup_input_import.
      + (* NoDup IR input *)
        admit.
      + (* NoDup op output *)
        admit.
      + (* NoDup IR output *)
        admit.
    - admit.
  Qed.
End RaftLinearizableProofs.
