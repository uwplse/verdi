Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import TraceRelations.

Require Import Raft.
Require Import CommonTheorems.
Require Import OutputCorrectInterface.
Require Import AppliedEntriesMonotonicInterface.
Require Import TraceUtil.

Require Import StateMachineCorrectInterface.
Require Import SortedInterface.
Require Import LastAppliedCommitIndexMatchingInterface.
Require Import LogMatchingInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section OutputCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {aemi : applied_entries_monotonic_interface}.
  Context {smci : state_machine_correct_interface}.
  Context {si : sorted_interface}.
  Context {lacimi : lastApplied_commitIndex_match_interface}.
  Context {lmi : log_matching_interface}.

  Section inner.
  Variables client id : nat.
  Variable out : output.

  Theorem in_output_trace_dec :
    forall tr : list (name * (raft_input + list raft_output)),
      {in_output_trace client id out tr} + {~ in_output_trace client id out tr}.
  Proof.
    unfold in_output_trace.
    intros.
    destruct (find (fun p => match snd p with
                               | inr l => match find (is_client_response client id out) l with
                                            | Some x => true
                                            | None => false
                                          end
                               | _ => false
                             end) tr) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      repeat break_match; try discriminate.
      find_apply_lem_hyp find_some. break_and.
      unfold is_client_response, in_output_list in *.
      break_match; try discriminate. do_bool. break_and. do_bool. subst.
      left. exists l, (fst p). clean.
      break_and. do_bool.
      break_if; try congruence. subst. intuition.
      find_reverse_rewrite.
      rewrite <- surjective_pairing.
      auto.
    - right. intro. break_exists. break_and.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. break_match; try discriminate.
      unfold in_output_list in *. break_exists.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. find_apply_lem_hyp Bool.andb_false_elim.
      repeat (intuition; do_bool).
      break_if; congruence.
  Qed.

  Lemma in_output_changed :
    forall tr o,
      ~ in_output_trace client id out tr ->
      in_output_trace client id out (tr ++ o) ->
      in_output_trace client id out o.
  Proof.
    intros. unfold in_output_trace in *.
    break_exists_exists.
    intuition. do_in_app; intuition.
    exfalso. eauto.
  Qed.

  Lemma in_output_list_split :
    forall l l',
      in_output_list client id out (l ++ l') ->
      in_output_list client id out l \/ in_output_list client id out l'.
  Proof.
    intros.
    unfold in_output_list in *.
    break_exists; do_in_app; intuition eauto.
  Qed.

  Lemma in_output_list_empty :
    ~ in_output_list client id out [].
  Proof.
    intuition.
  Qed.

  Lemma doLeader_key_in_output_list :
    forall st h os st' m,
      doLeader st h = (os, st', m) ->
      ~ in_output_list client id out os.
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty.
  Qed.

  Lemma handleInput_key_in_output_list :
    forall st h i os st' m,
      handleInput h i st = (os, st', m) ->
      ~ in_output_list client id out os.
  Proof.
    intros. unfold handleInput, handleTimeout, handleClientRequest, tryToBecomeLeader in *.
    repeat break_match; find_inversion; intuition eauto using in_output_list_empty;
    unfold in_output_list in *; break_exists; simpl in *; intuition; congruence.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Lemma deduplicate_log'_app :
    forall l l' ks,
      exists l'',
        deduplicate_log' (l ++ l') ks = deduplicate_log' l ks ++ l''.
  Proof.
    induction l; intros; simpl in *; intuition; eauto.
    repeat break_match; simpl in *; eauto;
    repeat find_insterU; break_exists; eexists; f_equal; eauto.
  Qed.


  Lemma deduplicate_log_app :
    forall l l',
      exists l'',
        deduplicate_log (l ++ l') = deduplicate_log l ++ l''.
  Proof.
    eauto using deduplicate_log'_app.
  Qed.


  Lemma in_output_trace_not_nil :
      in_output_trace client id out [] -> False.
  Proof.
    unfold in_output_trace.
    simpl. intros. break_exists. intuition.
  Qed.

  Lemma in_output_trace_singleton_inv :
    forall h l,
      in_output_trace client id out [(h, inr l)] ->
      in_output_list client id out l.
  Proof.
    unfold in_output_trace.
    intuition.
    break_exists. simpl in *. intuition.
  Qed.

  Lemma in_output_list_app_or :
    forall c i o l1 l2,
      in_output_list c i o (l1 ++ l2) ->
      in_output_list c i o l1 \/
      in_output_list c i o l2.
  Proof.
    unfold in_output_list.
    intuition.
  Qed.

  Lemma in_output_trace_inp_inv :
    forall h i tr,
      in_output_trace client id out ((h, inl i) :: tr) ->
      in_output_trace client id out tr.
  Proof.
    unfold in_output_trace.
    intuition. break_exists_exists. simpl in *. intuition.
  Qed.

  Lemma in_output_list_not_leader_singleton :
    forall a b,
      ~ in_output_list client id out [NotLeader a b].
  Proof.
    unfold in_output_list. simpl. intuition.
  Qed.

  Lemma handleInput_in_output_list :
    forall h i st os st' ms,
      handleInput h i st = (os, st', ms) ->
      ~ in_output_list client id out os.
  Proof.
    unfold handleInput, handleTimeout, handleInput, tryToBecomeLeader, handleClientRequest.
    intuition.
    repeat break_match; repeat find_inversion; eauto using in_output_trace_not_nil.
    - exfalso. eapply in_output_list_not_leader_singleton; eauto.
    - exfalso. eapply in_output_list_not_leader_singleton; eauto.
  Qed.

  Lemma in_output_list_cons_or :
    forall a b c l,
      in_output_list client id out (ClientResponse a b c :: l) ->
      (a = client /\ b = id /\ c = out) \/
      in_output_list client id out l.
  Proof.
    unfold in_output_list.
    simpl. intuition.
  Qed.

  Lemma assoc_Some_In :
    forall K V (K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}) k v l,
      assoc (V:=V) K_eq_dec l k = Some v ->
      In (k, v) l.
  Proof.
    induction l; simpl; intros; repeat break_match.
    - discriminate.
    - find_inversion. auto.
    - intuition.
  Qed.

  Lemma getLastId_Some_In :
    forall st c n o,
      getLastId st c = Some (n, o) ->
      In (c, (n, o)) (clientCache st).
  Proof.
    unfold getLastId.
    eauto using assoc_Some_In.
  Qed.

  Lemma middle_app_assoc :
    forall A xs (y : A) zs,
      xs ++ y :: zs = (xs ++ [y]) ++ zs.
  Proof.
    induction xs; intros; simpl; auto using f_equal.
  Qed.

  Lemma deduplicate_log'_snoc_drop_keys :
    forall es ks e n,
      assoc eq_nat_dec ks (eClient e) = Some n ->
      eId e <= n ->
      deduplicate_log' (es ++ [e]) ks = deduplicate_log' es ks.
  Proof.
    induction es; simpl; intuition; repeat break_match; repeat find_inversion; do_bool.
    - omega.
    - auto.
    - discriminate.
    - f_equal. destruct (eq_nat_dec (eClient a) (eClient e)).
      + repeat find_rewrite. find_injection.
        eapply IHes with (n := eId a); auto with *.
        now rewrite get_set_same.
      + eapply IHes; eauto.
        rewrite get_set_diff by auto. auto.
    - eauto.
    - f_equal. destruct (eq_nat_dec (eClient a) (eClient e)).
      + repeat find_rewrite. discriminate.
      + eapply IHes; eauto.
        rewrite get_set_diff by auto. auto.
  Qed.

  Lemma deduplicate_log'_snoc_drop_es :
    forall es ks e e',
      In e' es ->
      eClient e = eClient e' ->
      eId e <= eId e' ->
      deduplicate_log' (es ++ [e]) ks = deduplicate_log' es ks.
  Proof.
    induction es; simpl; intuition; repeat break_match; eauto using f_equal;
    repeat find_reverse_rewrite.
    - f_equal. subst. eapply deduplicate_log'_snoc_drop_keys; eauto.
      now rewrite get_set_same.
    - subst. do_bool. eapply deduplicate_log'_snoc_drop_keys; eauto; auto with *.
    - f_equal. subst. eapply deduplicate_log'_snoc_drop_keys; eauto.
      now rewrite get_set_same.
  Qed.

  Lemma deduplicate_log_snoc_drop :
    forall es e e',
      In e' es ->
      eClient e = eClient e' ->
      eId e <= eId e' ->
      deduplicate_log (es ++ [e]) = deduplicate_log es.
  Proof.
    intros. eapply deduplicate_log'_snoc_drop_es; eauto.
  Qed.


  Lemma deduplicate_log'_snoc_split :
    forall es ks e,
      (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) ->
      (forall i, assoc eq_nat_dec ks (eClient e) = Some i -> i < eId e) ->
      deduplicate_log' (es ++ [e]) ks = deduplicate_log' es ks ++ [e].
  Proof.
    induction es; intros; simpl in *; intuition.
    - break_match; simpl in *; auto.
      break_if; simpl in *; auto.
      do_bool.
      find_insterU. conclude_using eauto. omega.
    - repeat break_match; simpl in *; auto.
      + f_equal. eapply IHes; eauto.
        intros. do_bool.
        destruct (eq_nat_dec (eClient a) (eClient e)).
        * repeat find_rewrite.
          find_rewrite_lem get_set_same. find_injection.
          find_insterU. conclude_using eauto. intuition.
        * find_erewrite_lem get_set_diff.
          eauto.
      + f_equal. eapply IHes; eauto.
        intros. do_bool.
        destruct (eq_nat_dec (eClient a) (eClient e)).
        * repeat find_rewrite.
          find_rewrite_lem get_set_same. find_injection.
          match goal with
            | H : forall _, ?x = _ \/ _ -> _ |- _ =>
              specialize (H x)
          end.
          intuition.
        * find_erewrite_lem get_set_diff.
          eauto.
  Qed.

  Lemma deduplicate_log_snoc_split :
    forall es e,
      (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) ->
      deduplicate_log (es ++ [e]) = deduplicate_log es ++ [e].
  Proof.
    intros.
    eapply deduplicate_log'_snoc_split; eauto.
    intros. simpl in *. congruence.
  Qed.

  Lemma execute_log_app :
    forall xs ys,
      execute_log (xs ++ ys) = let (tr, st) := execute_log xs in execute_log' ys st tr.
  Proof.
    unfold execute_log.
    intros.
    rewrite execute_log'_app. auto.
  Qed.

  Lemma applyEntry_stateMachine_correct :
    forall st e l st' es,
      applyEntry st e = (l, st') ->
      stateMachine st = snd (execute_log (deduplicate_log es)) ->
      (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) ->
      stateMachine st' = snd (execute_log (deduplicate_log es ++ [e])).
  Proof.
    unfold applyEntry.
    intros.
    repeat break_match; repeat find_inversion. simpl.
    rewrite execute_log_app. simpl. repeat break_let.
    simpl in *. congruence.
  Qed.

  Lemma deduplicate_log_cases :
    forall es e,
      (deduplicate_log (es ++ [e]) = deduplicate_log es /\
       exists e', In e' es /\ eClient e' = eClient e /\ eId e <= eId e') \/
      (deduplicate_log (es ++ [e]) = deduplicate_log es ++ [e] /\
       (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e)).
  Proof.
    intros.
    destruct (find (fun e' => andb (eClient e' =? eClient e)
                                  (eId e <=? eId e')) es) eqn:?.
    - left. find_apply_lem_hyp find_some.
      repeat (break_and; do_bool).
      intuition eauto using deduplicate_log_snoc_drop.
    - right.
      match goal with
        | |- _ /\ ?P =>
          assert P; [|intuition; eauto using deduplicate_log_snoc_split]
      end.
      intros.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. repeat (do_bool; intuition).
  Qed.

  Lemma assoc_None :
    forall K V K_eq_dec (l : list (K * V)) k v,
      assoc K_eq_dec l k = None ->
      In (k, v) l ->
      False.
  Proof.
    intros; induction l; simpl in *; intuition.
    - subst. break_if; congruence.
    - break_match. subst. break_if; try congruence.
      auto.
  Qed.

  Lemma getLastId_None :
    forall st c i o,
      getLastId st c = None ->
      In (c, (i, o)) (clientCache st) ->
      False.
  Proof.
    intros.
    unfold getLastId in *.
    eauto using assoc_None.
  Qed.

  Lemma output_correct_monotonic :
    forall c i o xs ys,
      output_correct c i o xs ->
      output_correct c i o (xs ++ ys).
  Proof.
    unfold output_correct.
    intros.
    break_exists.
    intuition.
    pose proof (deduplicate_log_app xs ys). break_exists.
    repeat find_rewrite.
    rewrite app_ass in *. simpl in *.
    eexists. eexists. eexists. eexists. eexists.
    intuition eauto.
  Qed.

  Lemma applyEntry_output_correct :
    forall st e l st' o es,
      applyEntry st e = (l, st') ->
      In o l ->
      stateMachine st = snd (execute_log (deduplicate_log es)) ->
      (forall e', In e' es -> eClient e' = eClient e -> eId e' < eId e) ->
      output_correct (eClient e) (eId e) o (es ++ [e]).
  Proof.
    unfold applyEntry.
    intros.
    repeat break_match; repeat find_inversion.
    simpl in *. intuition.
    subst.
    unfold output_correct.
    rewrite deduplicate_log_snoc_split by auto.
    destruct (execute_log (deduplicate_log es)) eqn:?.
    eexists. eexists. exists []. eexists. eexists. intuition eauto.
    - rewrite execute_log_app. repeat find_rewrite. simpl in *. find_rewrite. eauto.
    - rewrite rev_app_distr. simpl. auto.
  Qed.

  Lemma cacheApplyEntry_output_correct :
    forall e es st l st' o,
      cacheApplyEntry st e = (l, st') ->
      In o l ->
      (forall c i o,
         getLastId st c = Some (i, o) ->
         output_correct c i o es) ->
      stateMachine st = snd (execute_log (deduplicate_log es)) ->
      (forall c i o e',
         getLastId st c = Some (i, o) ->
         In e' es ->
         eClient e' = c ->
         eId e' <= i) ->
      (forall e',
         In e' es ->
         exists i o,
           getLastId st (eClient e') = Some (i, o) /\
           eId e' <= i) ->
      output_correct (eClient e) (eId e) o (es ++ [e]).
  Proof.
    unfold cacheApplyEntry.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; intuition.
    - do_bool. subst. eauto using output_correct_monotonic, getLastId_Some_In.
    - eapply applyEntry_output_correct; eauto.
      do_bool. assert (n < eId e) by auto with *.
      intros. assert (eId e' <= n) by eauto. omega.
    - eapply applyEntry_output_correct; eauto.
      intros.
      find_apply_hyp_hyp.
      break_exists. break_and.
      repeat find_rewrite. discriminate.
  Qed.

  Lemma cacheApplyEntry_stateMachine_correct :
    forall st e l st' es,
      cacheApplyEntry st e = (l, st') ->
      stateMachine st = snd (execute_log (deduplicate_log es)) ->
      (forall c i o,
         getLastId st c = Some (i, o) ->
         exists e,
           In e es /\
           eClient e = c /\
           eId e = i) ->
      (forall c i o e',
         getLastId st c = Some (i, o) ->
         In e' es ->
         eClient e' = c ->
         eId e' <= i) ->
      (forall e',
         In e' es ->
         exists i o,
           getLastId st (eClient e') = Some (i, o) /\
           eId e' <= i) ->
      stateMachine st' = snd (execute_log (deduplicate_log (es ++ [e]))).
  Proof.
    intros.
    unfold cacheApplyEntry in *.
    repeat break_match; repeat find_inversion.
    - find_apply_hyp_hyp. break_exists. break_and.
      erewrite deduplicate_log_snoc_drop; eauto.
      do_bool. omega.
    - find_apply_hyp_hyp. break_exists. break_and.
      erewrite deduplicate_log_snoc_drop; eauto.
      do_bool. omega.
    - find_copy_apply_hyp_hyp. break_exists. break_and.
      pose proof (deduplicate_log_cases es e).
      intuition; break_exists; intuition; repeat find_rewrite.
      + do_bool. assert (eId x0 <= n) by eauto. omega.
      + eapply applyEntry_stateMachine_correct; eauto.
    - pose proof (deduplicate_log_cases es e).
      intuition; break_exists; intuition; repeat find_rewrite.
      + eapply_prop_hyp In In. break_exists. break_and.
        repeat find_rewrite. discriminate.
      + eapply applyEntry_stateMachine_correct; eauto.
  Qed.

  Lemma deduplicate_log_In_if :
    forall e l,
      In e (deduplicate_log l) ->
      In e l.
  Proof.
    unfold deduplicate_log.
    intros. eauto using deduplicate_log'_In_if.
  Qed.

  Lemma applyEntry_clientCache :
    forall st e l st',
      applyEntry st e = (l, st') ->
      let (out, _) := handler (eInput e) (stateMachine st)
      in (clientCache st' = assoc_set eq_nat_dec (clientCache st) (eClient e) (eId e, out) /\
          In out l).
  Proof.
    unfold applyEntry.
    intros.
    repeat break_match; repeat find_inversion. intuition.
  Qed.

  Lemma cacheApplyEntry_clientCache :
    forall st e l st',
      cacheApplyEntry st e = (l, st') ->
      (clientCache st' = clientCache st /\
       (exists i o, getLastId st (eClient e) = Some (i, o) /\
                    eId e <= i) ) \/
      ((let (out, _) := handler (eInput e) (stateMachine st)
       in (clientCache st' = assoc_set eq_nat_dec (clientCache st) (eClient e) (eId e, out) /\
          In out l)) /\ (getLastId st (eClient e) = None \/
                       (exists i o, getLastId st (eClient e) = Some (i, o) /\
                                    i < eId e))).
  Proof.
    unfold cacheApplyEntry.
    intros.
    repeat break_match_hyp; repeat find_inversion; do_bool; intuition eauto with *;
    right; (split; [solve [apply applyEntry_clientCache; auto]|]); auto.
    right. do_bool. eexists. eexists. intuition eauto. omega.
  Qed.

  Lemma getLastId_ext :
    forall st st' c,
      clientCache st' = clientCache st ->
      getLastId st' c = getLastId st c.
  Proof.
    unfold getLastId.
    intros.
    congruence.
  Qed.

  Lemma cacheAppliedEntry_clientCache_preserved :
    forall st e l st' c i o,
      cacheApplyEntry st e = (l, st') ->
      getLastId st c = Some (i, o) ->
      exists i' o',
        getLastId st' c = Some (i', o') /\
        i <= i'.
  Proof.
    intros.
    unfold cacheApplyEntry in *.
    repeat break_match; try find_inversion; simpl in *; repeat find_rewrite; eauto.
    - do_bool.
      unfold applyEntry in *.
      repeat break_match; find_inversion.
      unfold getLastId in *. simpl in *.
      destruct (eq_nat_dec (eClient e) c); subst.
      + rewrite get_set_same. find_rewrite.
        find_inversion. eauto.
      + rewrite get_set_diff in *; auto.
        repeat find_rewrite. eauto.
    - unfold applyEntry in *.
      repeat break_match; find_inversion.
      unfold getLastId in *. simpl in *.
      destruct (eq_nat_dec (eClient e) c); subst.
      + repeat find_rewrite.  congruence.
      + rewrite get_set_diff in *; auto.
        repeat find_rewrite. eauto.
  Qed.

  Lemma cacheAppliedEntry_clientCache_nondecreasing :
    forall st e l st' c i o i' o',
      cacheApplyEntry st e = (l, st') ->
      getLastId st c = Some (i, o) ->
      getLastId st' c = Some (i', o') ->
      i <= i'.
  Proof.
    intros.
    eapply cacheAppliedEntry_clientCache_preserved in H; eauto.
    break_exists. intuition.
  Qed.

  Lemma applyEntries_output_correct :
    forall l c i o h st os st' es,
      applyEntries h st l = (os, st') ->
      in_output_list c i o os ->
      (stateMachine st = snd (execute_log (deduplicate_log es))) ->
      (forall c i o,
         getLastId st c = Some (i, o) ->
         output_correct c i o es) ->
      (forall c i o e',
         getLastId st c = Some (i, o) ->
         In e' es -> eClient e' = c -> eId e' <= i) ->
      (forall e',
         In e' es ->
         exists i o,
           getLastId st (eClient e') = Some (i, o) /\ eId e' <= i) ->
      output_correct c i o (es ++ l).
  Proof.
    induction l; intros; simpl in *.
    - find_inversion. exfalso. eapply in_output_list_empty; eauto.
    - repeat break_let. find_inversion.
      find_apply_lem_hyp in_output_list_app_or.
      break_or_hyp.
      + break_if.
        * unfold in_output_list in *.
          do_in_map. find_inversion.
          rewrite middle_app_assoc. apply output_correct_monotonic.
          eapply cacheApplyEntry_output_correct; eauto.
        * exfalso. eapply in_output_list_empty; eauto.
      + rewrite middle_app_assoc. eapply IHl.
        * eauto.
        * auto.
        * eapply cacheApplyEntry_stateMachine_correct; eauto.
          intros.
          find_apply_hyp_hyp. unfold output_correct in *.
          break_exists. break_and.
          eexists. intuition eauto.
          eapply deduplicate_log_In_if.
          eauto with *.
        * find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
          { intros. break_or_hyp.
            - break_and.
              apply output_correct_monotonic.
              unfold getLastId in *. repeat find_rewrite. eauto.
            - break_let. break_and.
              unfold getLastId in *.
              repeat find_rewrite.
              destruct (eq_nat_dec (eClient a) c0).
              + subst.  rewrite get_set_same in *. find_inversion.
                eapply cacheApplyEntry_output_correct; eauto.
              + rewrite get_set_diff in * by auto. eauto using output_correct_monotonic.
          }
        * intros.
          do_in_app. simpl in *.
          { intuition.
            - eapply_prop_hyp In In. break_exists. break_and. subst.
              eauto using le_trans, cacheAppliedEntry_clientCache_nondecreasing.
            - subst. find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
              intuition.
              + break_exists. break_and.
                eauto using le_trans, cacheAppliedEntry_clientCache_nondecreasing.
              + unfold getLastId in *. break_let. break_and. repeat find_rewrite.
                rewrite get_set_same in *. find_inversion. auto.
              + unfold getLastId in *. break_let. break_and.
                repeat find_rewrite.
                rewrite get_set_same in *. find_inversion. auto.
          }
        * intros.
          do_in_app. simpl in *.
          { intuition.
            - eapply_prop_hyp In In. break_exists. break_and.
              find_copy_eapply_lem_hyp cacheAppliedEntry_clientCache_preserved; eauto.
              break_exists_exists. intuition.
            - subst. find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
              intuition.
              + break_exists. break_and.
                find_copy_eapply_lem_hyp cacheAppliedEntry_clientCache_preserved; eauto.
                break_exists_exists. intuition.
              + break_let. break_and. unfold getLastId. repeat find_rewrite.
                eexists. eexists. rewrite get_set_same. intuition eauto.
              + break_let. break_and. unfold getLastId. repeat find_rewrite.
                eexists. eexists. rewrite get_set_same. intuition eauto.
          }
  Qed.

  Lemma cacheApplyEntry_spec :
    forall st a l st',
      cacheApplyEntry st a = (l, st') ->
      log st' = log st /\
      lastApplied st' = lastApplied st /\
      commitIndex st' = commitIndex st.
  Proof.
    intros. unfold cacheApplyEntry, applyEntry in *.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma applyEntries_spec :
    forall es h st os st',
      applyEntries h st es = (os, st') ->
      log st' = log st /\
      lastApplied st' = lastApplied st /\
      commitIndex st' = commitIndex st.
  Proof.
    induction es; intros; simpl in *.
    - find_inversion. auto.
    - repeat break_match; find_inversion;
      find_apply_hyp_hyp;
      find_apply_lem_hyp cacheApplyEntry_spec;
      intuition; repeat find_rewrite; auto.
  Qed.

  Lemma output_correct_prefix :
    forall l1 l2 client id out,
      Prefix l1 l2 ->
      output_correct client id out l1 ->
      output_correct client id out l2.
  Proof.
    intros.
    find_apply_lem_hyp Prefix_exists_rest.
    break_exists. subst.
    eauto using output_correct_monotonic.
  Qed.

  Lemma entries_contiguous :
    forall net,
      raft_intermediate_reachable net ->
      (forall h, contiguous_range_exact_lo (log (nwState net h)) 0).
  Proof.
    intros. find_apply_lem_hyp log_matching_invariant.
    unfold log_matching, log_matching_hosts in *.
    intuition.
    unfold contiguous_range_exact_lo. intuition; eauto.
    find_apply_hyp_hyp. omega.
  Qed.

  Lemma doGenericServer_output_correct :
    forall h ps sigma os st' ms,
      raft_intermediate_reachable (mkNetwork ps sigma) ->
      doGenericServer h (sigma h) = (os, st', ms) ->
      in_output_list client id out os ->
      output_correct client id out (applied_entries (update sigma h st')).
  Proof.
    intros.
    find_copy_apply_lem_hyp logs_sorted_invariant.
    pose proof entries_contiguous.
    match goal with
      | H : context [contiguous_range_exact_lo] |- _ =>
        specialize (H ({| nwPackets := ps; nwState := sigma |}))
    end.
    concludes. simpl in *.
    find_copy_apply_lem_hyp state_machine_correct_invariant.
    unfold state_machine_correct in *. intuition.
    unfold logs_sorted in *. intuition.
    unfold doGenericServer in *.
    break_let. find_inversion.
    find_copy_apply_lem_hyp applyEntries_spec. intuition. repeat find_rewrite.
    eapply applyEntries_output_correct
    with (es := rev (removeAfterIndex (log (sigma h)) (lastApplied (sigma h)))) in Heqp; eauto.
    - rewrite <- rev_app_distr in *.
      eapply output_correct_prefix; eauto.
      break_if.
      + do_bool.
        erewrite findGtIndex_removeAfterIndex_i_lt_i' in *; eauto.
        match goal with
          | |- context [applied_entries (update ?sigma ?h ?st)] =>
            pose proof applied_entries_update sigma h st
        end. conclude_using intuition.
        intuition; simpl in *;
        unfold raft_data in *; simpl in *; find_rewrite; auto using Prefix_refl.
        unfold applied_entries in *.
        break_exists. intuition. repeat find_rewrite.
        eapply contiguous_sorted_subset_prefix; eauto using removeAfterIndex_contiguous, removeAfterIndex_sorted.
        intros.
        find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
        find_apply_lem_hyp removeAfterIndex_in.
        apply removeAfterIndex_le_In; eauto; try omega.
        find_copy_apply_lem_hyp commitIndex_lastApplied_match_invariant.
        unfold commitIndex_lastApplied_match in *. simpl in *.
        match goal with
          | _ : ?x >= ?y |- _ =>
            assert (y <= x) by omega
        end.
        eapply_prop_hyp le le; eauto. intuition.
      + do_bool.
        erewrite findGtIndex_removeAfterIndex_i'_le_i in *; eauto.
        match goal with
          | |- context [applied_entries (update ?sigma ?h ?st)] =>
            pose proof applied_entries_update sigma h st
        end. conclude_using intuition.
        intuition; simpl in *;
        unfold raft_data in *; simpl in *; find_rewrite; auto using Prefix_refl.
        unfold applied_entries in *.
        break_exists. intuition. repeat find_rewrite.
        eapply contiguous_sorted_subset_prefix; eauto using removeAfterIndex_contiguous, removeAfterIndex_sorted.
        intros.
        find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
        find_apply_lem_hyp removeAfterIndex_in.
        apply removeAfterIndex_le_In; eauto; try omega.
        find_copy_apply_lem_hyp lastApplied_lastApplied_match_invariant.
        unfold lastApplied_lastApplied_match in *. simpl in *.
        match goal with
          | _ : ?x >= ?y |- _ =>
            assert (y <= x) by omega
        end.
        eapply_prop_hyp le le; eauto. intuition.
    - unfold client_cache_complete in *.
      simpl in *.
      intros. subst.
      find_apply_lem_hyp In_rev. find_apply_hyp_hyp.
      break_exists. intuition.
    - intros. find_apply_lem_hyp In_rev. eauto.
  Qed.

  Ltac intermediate_networks :=
    match goal with
      | Hdgs : doGenericServer ?h ?st' = _,
               Hdl : doLeader ?st ?h = _ |- context [update (nwState ?net) ?h ?st''] =>
        replace st with (update (nwState net) h st h) in Hdl by eauto using update_eq;
          replace st' with (update (update (nwState net) h st) h st' h) in Hdgs by eauto using update_eq;
          let H := fresh "H" in
          assert (update (nwState net) h st'' =
                  update (update (update (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H
    end.

  Lemma in_output_trace_step_output_correct :
    forall failed failed' (net net' : network (params := @multi_params _ _ raft_params)) os,
      in_output_trace client id out os ->
      @raft_intermediate_reachable _ _ raft_params net ->
      step_f (failed, net) (failed', net') os ->
      output_correct client id out (applied_entries (nwState net')).
  Proof.
    intros.
    match goal with
      | [ H : context [ step_f _ _ _ ] |- _ ] => invcs H
    end.
    - unfold RaftNetHandler in *. repeat break_let. repeat find_inversion.
      find_apply_lem_hyp in_output_trace_singleton_inv.
      find_apply_lem_hyp in_output_list_app_or.
      intuition.
      + exfalso. eapply doLeader_key_in_output_list; eauto.      
      + find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
        find_copy_eapply_lem_hyp RIR_doLeader; simpl; rewrite_update; eauto.
        intermediate_networks.
        find_copy_apply_lem_hyp doLeader_appliedEntries. 
        eapply doGenericServer_output_correct; eauto.
    - unfold RaftInputHandler in *. repeat break_let. repeat find_inversion.
      find_apply_lem_hyp in_output_trace_inp_inv.
      find_apply_lem_hyp in_output_trace_singleton_inv.
      find_apply_lem_hyp in_output_list_app_or.
      intuition.
      + exfalso. eapply handleInput_in_output_list; eauto.
      + find_apply_lem_hyp in_output_list_app_or.
        intuition.
        * exfalso. eapply doLeader_key_in_output_list; eauto.
          * find_copy_eapply_lem_hyp RIR_handleInput; eauto.
            find_copy_eapply_lem_hyp RIR_doLeader; simpl; rewrite_update; eauto.
            intermediate_networks.
            find_copy_apply_lem_hyp doLeader_appliedEntries. 
            eapply doGenericServer_output_correct; eauto.
    - exfalso. eauto using in_output_trace_not_nil.
    - exfalso. eauto using in_output_trace_not_nil.
    - exfalso. eauto using in_output_trace_not_nil.
    - exfalso. eauto using in_output_trace_not_nil.
  Qed.

  Instance TR : TraceRelation step_f :=
    {
      init := step_f_init;
      T := in_output_trace client id out ;
      T_dec := in_output_trace_dec ;
      R := fun s => let (_, net) := s in
                    output_correct client id out (applied_entries (nwState net))
    }.
  Proof.
    - intros. repeat break_let. subst.
      find_eapply_lem_hyp applied_entries_monotonic';
        eauto using step_f_star_raft_intermediate_reachable.
      unfold output_correct in *.
      break_exists.
      repeat find_rewrite.
      match goal with
          | [ |- context [ deduplicate_log (?l ++ ?l') ] ] =>
            pose proof deduplicate_log_app l l'; break_exists; find_rewrite
      end.
      repeat eexists; intuition eauto; repeat find_rewrite; auto.
      rewrite app_ass. simpl. repeat f_equal.
  - unfold in_output_trace in *. intuition.
    break_exists; intuition.
  - intros.
    break_let. subst.
    find_apply_lem_hyp in_output_changed; auto.
    destruct s.
    eauto using in_output_trace_step_output_correct, step_f_star_raft_intermediate_reachable.
  Defined.

  Theorem output_correct :
    forall  failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      in_output_trace client id out tr ->
      output_correct client id out (applied_entries (nwState net)).
  Proof.
    intros. pose proof (trace_relations_work (failed, net) tr).
    repeat concludes.
    auto.
  Qed.
  End inner.

  Instance oci : output_correct_interface.
  Proof.
    split.
    exact output_correct.
  Qed.
End OutputCorrect.
