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
Require Import LogMatchingInterface.
Require Import StateMachineSafetyInterface.
Require Import AppliedEntriesMonotonicInterface.
Require Import MaxIndexSanityInterface.
Require Import StateMachineCorrectInterface.
Require Import LastAppliedCommitIndexMatchingInterface.
Require Import TraceUtil.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SortedInterface.

Require Import OutputGreatestIdInterface.

Section OutputGreatestId.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lmi : log_matching_interface}.
  Context {si : sorted_interface}.
  Context {aemi : applied_entries_monotonic_interface}.
  Context {smsi : state_machine_safety_interface}.
  Context {misi : max_index_sanity_interface}.
  Context {smci : state_machine_correct_interface}.
  Context {lacimi : lastApplied_commitIndex_match_interface}.


  Lemma in_output_changed :
    forall client id tr o,
      ~ key_in_output_trace client id tr ->
      key_in_output_trace client id (tr ++ o) ->
      key_in_output_trace client id o.
  Proof.
    intros. unfold key_in_output_trace in *.
    break_exists_exists.
    intuition. do_in_app; intuition.
    exfalso. eauto.
  Qed.

  Lemma key_in_output_list_split :
    forall client id l l',
      key_in_output_list client id (l ++ l') ->
      key_in_output_list client id l \/ key_in_output_list client id l'.
  Proof.
    intros.
    unfold key_in_output_list in *.
    break_exists; do_in_app; intuition eauto.
  Qed.

  Lemma key_in_output_list_empty :
    forall client id,
      ~ key_in_output_list client id [].
  Proof.
    intuition.
    unfold key_in_output_list in *.
    break_exists; intuition.
  Qed.

  Lemma doLeader_key_in_output_list :
    forall st h out st' m client id,
      doLeader st h = (out, st', m) ->
      ~ key_in_output_list client id out.
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; intuition;
    find_apply_lem_hyp key_in_output_list_empty; auto.
  Qed.

  Lemma handleInput_key_in_output_list :
    forall st h i out st' m client id,
      handleInput h i st = (out, st', m) ->
      ~ key_in_output_list client id out.
  Proof.
    intros. unfold handleInput, handleTimeout, handleClientRequest, tryToBecomeLeader in *.
    repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty;
    unfold key_in_output_list in *; break_exists; simpl in *; intuition; congruence.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Lemma has_key_own_key :
    forall e,
      has_key (eClient e) (eId e) e = true.
  Proof.
    intros. unfold has_key. break_match; subst; simpl in *.
    repeat (do_bool; intuition).
  Qed.

  Lemma has_key_true_necessary :
    forall client id e,
      has_key client id e = true ->
      eClient e = client /\ eId e = id.
  Proof.
    intros. unfold has_key in *. break_match.
    simpl in *. subst.
    repeat (do_bool; intuition).
  Qed.


  Lemma applyEntries_cache :
    forall l h st os st' o client id id' o',
      id < id' ->
      applyEntries h st l = (os, st') ->
      In (ClientResponse client id o) os ->
      getLastId st client <> Some (id', o').
  Proof.
    induction l; intros; simpl in *; intuition.
    - find_inversion. simpl in *. intuition.
    - unfold cacheApplyEntry, applyEntry in *.
      repeat break_match; repeat find_inversion; simpl in *; intuition; eauto;
      try solve 
          [find_inversion; find_rewrite; find_inversion; do_bool; omega];
      try solve [find_inversion; repeat find_rewrite; congruence].
      + do_bool. destruct (eq_nat_dec (eClient a) client).
        * subst. find_rewrite. find_inversion.
          eapply IHl; [eapply lt_le_trans; eauto|idtac|idtac|]; eauto.
          unfold getLastId.
          simpl. eauto using get_set_same.
        * eapply IHl; eauto.
          unfold getLastId in *.
          simpl. rewrite get_set_diff; eauto.
      + do_bool. destruct (eq_nat_dec (eClient a) client).
        * repeat find_rewrite. congruence.
        * eapply IHl; eauto.
          unfold getLastId in *.
          simpl. rewrite get_set_diff; eauto.
      + do_bool. destruct (eq_nat_dec (eClient a) client).
        * repeat find_rewrite. find_inversion.
          eapply IHl; [eapply lt_le_trans; eauto|idtac|idtac|]; eauto.
          unfold getLastId.
          simpl. eauto using get_set_same.
        * eapply IHl; eauto.
          unfold getLastId in *.
          simpl. rewrite get_set_diff; eauto.
      + do_bool. destruct (eq_nat_dec (eClient a) client).
        * repeat find_rewrite. congruence.
        * eapply IHl; eauto.
          unfold getLastId in *.
          simpl. rewrite get_set_diff; eauto.
  Qed.
  
  Lemma applyEntries_before :
    forall l h st os st' o client id id',
      id < id' ->
      applyEntries h st l = (os, st') ->
      In (ClientResponse client id o) os ->
      before_func (has_key client id) (has_key client id') l.
  Proof.
    induction l; intros; simpl in *; intuition.
    - find_inversion. simpl in *. intuition.
    - repeat break_match.
      + subst.
        find_inversion. do_in_app. intuition.
        * do_in_map. find_inversion. eauto using has_key_own_key.
        * { destruct (has_key client id' a) eqn:?; eauto.
            exfalso.
            unfold cacheApplyEntry, applyEntry in *.
            find_apply_lem_hyp has_key_true_necessary. intuition.
            repeat break_match; repeat find_rewrite; find_inversion; do_bool; subst.
            - find_eapply_lem_hyp applyEntries_cache; auto;
              [eapply lt_trans; [|eauto]; eauto|idtac|]; eauto.
            - find_eapply_lem_hyp applyEntries_cache; eauto.
            - find_eapply_lem_hyp applyEntries_cache; eauto;
              unfold getLastId in *; simpl in *; eauto using get_set_same.
            - find_eapply_lem_hyp applyEntries_cache; eauto;
              unfold getLastId in *; simpl in *; eauto using get_set_same.
          }
      + simpl in *. find_inversion.
        { destruct (has_key client id' a) eqn:?; eauto.
            exfalso.
            unfold cacheApplyEntry, applyEntry in *.
            find_apply_lem_hyp has_key_true_necessary. intuition.
            repeat break_match; repeat find_rewrite; find_inversion; do_bool; subst.
            - find_eapply_lem_hyp applyEntries_cache; auto;
              [eapply lt_trans; [|eauto]; eauto|idtac|]; eauto.
            - find_eapply_lem_hyp applyEntries_cache; eauto.
            - find_eapply_lem_hyp applyEntries_cache; eauto;
              unfold getLastId in *; simpl in *; eauto using get_set_same.
            - find_eapply_lem_hyp applyEntries_cache; eauto;
              unfold getLastId in *; simpl in *; eauto using get_set_same.
          }
  Qed.

  Lemma before_func_prepend :
    forall A f g (l : list A) l',
      before_func f g l ->
      (forall x, In x l' -> g x = false) ->
      before_func f g (l' ++ l).
  Proof.
    induction l'; intros; simpl in *; intuition.
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

  Lemma before_func_prefix :
    forall A f g (l : list A) l',
      Prefix l l' ->
      before_func f g l ->
      before_func f g l'.
  Proof.
    intros.
    find_apply_lem_hyp Prefix_exists_rest.
    break_exists; subst.
    eauto using before_func_app.
  Qed.
  
  Lemma doGenericServer_key_in_output_list :
    forall net h os st' ms id' client id,
      raft_intermediate_reachable net ->
      doGenericServer h (nwState net h) = (os, st', ms) ->
      key_in_output_list client id os ->
      id < id' ->
      before_func (has_key client id) (has_key client id') (applied_entries (update (nwState net) h st')).
  Proof.
    intros.
    find_copy_apply_lem_hyp logs_sorted_invariant.
    pose proof entries_contiguous.
    match goal with
      | H : context [contiguous_range_exact_lo] |- _ =>
        specialize (H net)
    end.
    concludes. simpl in *.
    find_copy_apply_lem_hyp state_machine_correct_invariant.
    unfold state_machine_correct in *. intuition.
    unfold logs_sorted in *. intuition.
    unfold key_in_output_list in *.
    match goal with | H : exists _, _ |- _ => destruct H as [o] end.
    unfold doGenericServer in *. break_let. simpl in *.
    find_inversion. simpl in *. find_copy_eapply_lem_hyp applyEntries_before; eauto.
    match goal with
      | H : before_func _ _ ?l |- _=>
        eapply before_func_prepend with
        (l' := (rev (removeAfterIndex (log (nwState net h))
                                      (lastApplied (nwState net h)))))
          in H
    end; eauto;
    [|intros;
       find_apply_lem_hyp In_rev;
       apply Bool.not_true_iff_false;
       intuition; unfold has_key in *;
       break_match; repeat (do_bool; intuition); simpl in *;
       eapply_prop_hyp client_cache_complete In; eauto;
       break_exists; intuition; simpl in *;
       subst;
       match goal with
         | Ha : context [applyEntries], Hg : getLastId _ _ = Some (?x, _) |- _ =>
           eapply applyEntries_cache with (id' := x) in Ha
       end; eauto; omega;
       intuition; find_rewrite; repeat find_rewrite].
    rewrite <- rev_app_distr in *.
    eapply before_func_prefix; eauto.
    use_applyEntries_spec. subst. simpl in *.
    break_if.
    - do_bool.
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
     - do_bool.
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
  Qed.

  
  Lemma output_implies_greatest :
    forall failed net failed' net' o client id id',
      raft_intermediate_reachable net ->
      @step_f _ _ failure_params (failed, net) (failed', net') o ->
      key_in_output_trace client id o ->
      id < id' ->
      before_func (has_key client id) (has_key client id') (applied_entries (nwState net')).
  Proof.
    intros.
    invcs H0; simpl in *;
    try match goal with
          | _ : key_in_output_trace _ _ [] |- _ =>
            unfold key_in_output_trace in *; break_exists; simpl in *; intuition
        end.
    - unfold key_in_output_trace in *.
      break_exists; simpl in *; intuition.
      find_inversion.
      unfold RaftNetHandler in *.
      repeat break_let. repeat find_inversion. simpl in *.
      find_eapply_lem_hyp RIR_handleMessage; eauto.
      find_copy_eapply_lem_hyp RIR_doLeader; simpl in *; rewrite_update; eauto.
      find_apply_lem_hyp key_in_output_list_split.
      intuition; [exfalso; eapply doLeader_key_in_output_list; eauto|].
      match goal with
        | _ : doLeader ?st ?h = _, _ : doGenericServer _ ?d = _ |- _ =>
          replace st with ((update (nwState net) h st) h) in *;
            [|rewrite_update; auto]
      end.
      find_apply_lem_hyp doLeader_appliedEntries.
      rewrite_update. repeat find_rewrite_lem update_overwrite.
      unfold data in *. simpl in *.
      match goal with
        | _ : raft_intermediate_reachable (mkNetwork ?ps ?st),
              H : doGenericServer ?h ?r = _ |- _ =>
          replace r with (nwState (mkNetwork ps st) h) in H by (simpl in *; rewrite_update; auto)
      end.
      find_eapply_lem_hyp doGenericServer_key_in_output_list; [|idtac|eauto|]; eauto.
      simpl in *. find_rewrite_lem update_overwrite. auto.
    - unfold key_in_output_trace in *.
      break_exists; simpl in *; intuition.
      find_inversion.
      unfold RaftInputHandler in *.
      repeat break_let. repeat find_inversion. simpl in *.
      find_copy_eapply_lem_hyp RIR_handleInput; eauto.
      find_copy_eapply_lem_hyp RIR_doLeader; simpl in *; rewrite_update; eauto.
      find_apply_lem_hyp key_in_output_list_split.
      intuition; [exfalso; eapply handleInput_key_in_output_list; eauto|].
      find_apply_lem_hyp key_in_output_list_split.
      intuition; [exfalso; eapply doLeader_key_in_output_list; eauto|].
      match goal with
        | _ : doLeader ?st ?h = _, _ : doGenericServer _ ?d = _ |- _ =>
          replace st with ((update (nwState net) h st) h) in *;
            [|rewrite_update; auto]
      end.
      find_apply_lem_hyp doLeader_appliedEntries.
      rewrite_update. repeat find_rewrite_lem update_overwrite.
      unfold data in *. simpl in *.
      match goal with
        | _ : raft_intermediate_reachable (mkNetwork ?ps ?st),
              H : doGenericServer ?h ?r = _ |- _ =>
          replace r with (nwState (mkNetwork ps st) h) in H by (simpl in *; rewrite_update; auto)
      end.
      find_eapply_lem_hyp doGenericServer_key_in_output_list; [|idtac|eauto|]; eauto.
      simpl in *. find_rewrite_lem update_overwrite. auto.
  Qed.

  Section inner.
    Variables client id id' : nat.
    Variable id_lt_id' : id < id'.
    
  
    Instance TR : TraceRelation step_f :=
      {
        init := step_f_init;
        T := key_in_output_trace client id ;
        T_dec := key_in_output_trace_dec client id ;
        R := fun s => before_func (has_key client id) (has_key client id') (applied_entries (nwState (snd s)))
      }.
    Proof.
      - intros.
        destruct s as (failed, net).
        destruct s' as (failed', net'). simpl in *.
        find_apply_lem_hyp step_f_star_raft_intermediate_reachable.
        find_eapply_lem_hyp applied_entries_monotonic'; eauto.
        break_exists; repeat find_rewrite.
        eauto using before_func_app.
      - unfold key_in_output_trace in *. intuition.
        break_exists; intuition.
      - intros.
        destruct s as [failed net].
        destruct s' as [failed' net']. simpl in *.
        find_apply_lem_hyp step_f_star_raft_intermediate_reachable.
        find_apply_lem_hyp in_output_changed; auto.
        eauto using output_implies_greatest.
    Defined.

  Theorem output_greatest_id :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      key_in_output_trace client id tr ->
      before_func (has_key client id) (has_key client id') (applied_entries (nwState net)).
  Proof.
    intros. pose proof (trace_relations_work (failed, net) tr).
    concludes. intuition.
  Qed.
  End inner.

  Instance ogii : output_greatest_id_interface.
  Proof.
    split. unfold greatest_id_for_client. intros.
    eauto using output_greatest_id.
  Qed.
End OutputGreatestId.
