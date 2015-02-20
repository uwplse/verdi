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
Require Import LogMatching.
Require Import StateMachineSafety.
Require Import AppliedEntriesMonotonic.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section OutputImpliesApplied.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Variables client id : nat.

  Definition in_output_list (os : list raft_output) :=
    exists o,
      In (ClientResponse client id o) os.

  Definition in_output_list_dec (os : list raft_output) :
    {in_output_list os} + {~ in_output_list os}.
  Proof.
    induction os.
    - right. intuition. unfold in_output_list in *. break_exists. intuition.
    - intuition.
      + left. unfold in_output_list in *. break_exists; eexists; simpl; intuition eauto.
      + destruct a.
        * right. intros.
          unfold in_output_list in *.
          break_exists; simpl in *; intuition eauto; congruence.
        * { destruct (eq_nat_dec n client); destruct (eq_nat_dec n0 id); subst; intuition.
            - left. unfold in_output_list. eexists; simpl; intuition eauto.
            - right. intros. unfold in_output_list in *.
              break_exists; simpl in *; intuition eauto; find_inversion; intuition.
            - right. intros. unfold in_output_list in *.
              break_exists; simpl in *; intuition eauto; find_inversion; intuition.
            - right. intros. unfold in_output_list in *.
              break_exists; simpl in *; intuition eauto; find_inversion; intuition.
          }
  Qed.

  Definition in_output (tr : list (name * (raft_input + list raft_output))) : Prop :=
    exists os h,
      In (h, inr os) tr /\
      in_output_list os.

  Theorem in_output_dec :
    forall tr : list (name * (raft_input + list raft_output)),
      {in_output tr} + {~ in_output tr}.
  Proof.
    intros. induction tr.
    - right. intuition. unfold in_output in *. break_exists.
      intuition.
    - intuition.
      + left. unfold in_output in *. unfold in_output_list in *.
        repeat (break_exists; intuition); repeat eexists; simpl; intuition eauto.
      + left. unfold in_output in *.
        break_exists. exists x. exists x0. 
        intuition.
      + right. intros. unfold in_output in *.
        break_exists; simpl in *; intuition eauto; try (find_inversion; congruence).
      + destruct (in_output_list_dec b1).
        * left. unfold in_output. exists b1; eexists; simpl; intuition eauto.
        * right. intros. unfold in_output in *.
          break_exists; simpl in *; intuition eauto; find_inversion; intuition.
  Qed.

  Lemma in_output_changed :
    forall tr o,
      ~in_output tr ->
      in_output (tr ++ o) ->
      in_output o.
  Proof.
    intros. unfold in_output in *.
    break_exists_exists.
    intuition. do_in_app; intuition.
    exfalso. eauto.
  Qed.

  Lemma in_output_list_split :
    forall l l',
      in_output_list (l ++ l') ->
      in_output_list l \/ in_output_list l'.
  Proof.
    intros.
    unfold in_output_list in *.
    break_exists; do_in_app; intuition eauto.
  Qed.

  Lemma in_output_list_empty :
    ~ in_output_list [].
  Proof.
    intuition.
    unfold in_output_list in *.
    break_exists; intuition.
  Qed.

  Lemma doLeader_in_output_list :
    forall st h out st' m,
      doLeader st h = (out, st', m) ->
      ~ in_output_list out.
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; intuition eauto using in_output_list_empty.
  Qed.

  Lemma handleInput_in_output_list :
    forall st h i out st' m,
      handleInput h i st = (out, st', m) ->
      ~ in_output_list out.
  Proof.
    intros. unfold handleInput, handleTimeout, handleClientRequest, tryToBecomeLeader in *.
    repeat break_match; find_inversion; intuition eauto using in_output_list_empty;
    unfold in_output_list in *; break_exists; simpl in *; intuition; congruence.
  Qed.
  
  Definition in_applied_entries (net : network) : Prop :=
    exists e,
      eClient e = client /\
      eId e = id /\
      In e (applied_entries (nwState net)).

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.
  
  Lemma applyEntries_In :
    forall l h st os st' o,
      applyEntries h st l = (os, st') ->
      In (ClientResponse client id o) os ->
      exists e : entry,
        eClient e = client /\
        eId e = id /\
        In e l.
  Proof.
    induction l; intros.
    - simpl in *.
      find_inversion; simpl in *; intuition.
    - simpl in *. repeat break_let.
      break_if; find_inversion; simpl in *; intuition;
      try find_inversion; eauto;
      find_eapply_lem_hyp IHl; eauto;
      break_exists_exists; intuition.
  Qed.

  Lemma doGenericServer_in_output_list :
    forall net h os st' ms,
      raft_intermediate_reachable net ->
      doGenericServer h (nwState net h) = (os, st', ms) ->
      in_output_list os ->
      exists e : entry,
        eClient e = client /\
        eId e = id /\ In e (applied_entries (update (nwState net) h st')).
  Proof.
    intros. unfold in_output_list in *.
    match goal with | H : exists _, _ |- _ => destruct H as [o] end.
    unfold doGenericServer in *. break_let. simpl in *.
    find_inversion. simpl in *. find_eapply_lem_hyp applyEntries_In; eauto.
    break_exists_exists. intuition.
    find_apply_lem_hyp In_rev.
    find_apply_lem_hyp filter_In.
    intuition. repeat (do_bool; intuition).
    break_if; simpl in *; do_bool; [|omega].
    match goal with
      | |- context [update ?st ?h ?st'] =>
        pose proof applied_entries_update st h st'
    end. forwards; [simpl in *; intuition|]. concludes.
    intuition.
    - simpl in *. unfold raft_data in *. simpl in *.
      find_rewrite.
      match goal with | H : applied_entries _ = applied_entries _ |- _ => clear H end.
      break_exists. intuition.
      unfold applied_entries in *.
      find_rewrite.
      match goal with
        | |- In _ (rev ?l') => apply in_rev with (l := l')
      end.
      apply removeAfterIndex_le_In; intuition.
      find_copy_apply_lem_hyp log_matching_invariant.
      find_apply_lem_hyp state_machine_safety_invariant.
      unfold state_machine_safety, log_matching, log_matching_hosts in *.
      intuition.
      match goal with
        | [ e : entry, H : forall _ _, _ <= _ <= _ -> _, Hm : maxIndex_lastApplied _
                                                   |- In _ (log (_ _ ?h)) ] =>
          specialize (H h (eIndex e)); specialize (Hm h); forward H; intuition
      end. break_exists. intuition.
      find_apply_lem_hyp findGtIndex_necessary. intuition.
      match goal with
        | _ : In ?e1 (log _), _ : In ?e2 (log _) |- _ =>
          cut (e1 = e2); [intros; subst; auto|]
      end. eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto.
      omega.
    - simpl in *. unfold raft_data in *. simpl in *.
      find_rewrite.
      match goal with
        | |- In _ (rev ?l') => apply in_rev with (l := l')
      end.
      find_apply_lem_hyp findGtIndex_necessary.
      intuition.
      eauto using removeAfterIndex_le_In.
  Qed.
  
  Lemma output_implies_in_applied_entries :
    forall failed net failed' net' o,
      raft_intermediate_reachable net ->
      step_f (failed, net) (failed', net') o ->
      in_output o ->
      in_applied_entries net'.
  Proof.
    intros.
    invcs H0; simpl in *;
    try match goal with
          | _ : in_output [] |- _ =>
            unfold in_output in *; break_exists; simpl in *; intuition
        end.
    - unfold in_output in *.
      break_exists; simpl in *; intuition.
      find_inversion.
      unfold in_applied_entries in *. simpl in *.
      unfold RaftNetHandler in *.
      repeat break_let. repeat find_inversion. simpl in *.
      find_eapply_lem_hyp RIR_handleMessage; eauto.
      find_apply_lem_hyp in_output_list_split.
      intuition; [|exfalso; eapply doLeader_in_output_list; eauto].
      match goal with
        | _ : doLeader ?st ?h = _, _ : doGenericServer _ ?d = _ |- _ =>
          replace st with ((update (nwState net) h st) h) in *;
            [|rewrite_update; auto]
      end.
      find_apply_lem_hyp doLeader_appliedEntries.
      rewrite_update. repeat find_rewrite_lem update_overwrite.
      unfold data in *. simpl in *.
      find_rewrite.
      match goal with
        | _ : raft_intermediate_reachable (mkNetwork ?ps ?st),
          H : doGenericServer ?h ?r = _ |- _ =>
          replace r with (nwState (mkNetwork ps st) h) in H by (simpl in *; rewrite_update; auto)
      end.
      find_eapply_lem_hyp doGenericServer_in_output_list; [|idtac|eauto]; eauto.
      break_exists_exists. intuition. simpl in *.
      find_rewrite_lem update_overwrite. auto.
    - unfold in_output in *.
      break_exists; simpl in *; intuition; find_inversion.
      unfold in_applied_entries in *. simpl in *.
      unfold RaftInputHandler in *.
      repeat break_let. repeat find_inversion. simpl in *.
      find_copy_eapply_lem_hyp RIR_handleInput; eauto.
      find_apply_lem_hyp in_output_list_split.
      intuition; [exfalso; eapply handleInput_in_output_list; eauto|].
      find_apply_lem_hyp in_output_list_split.
      intuition; [|exfalso; eapply doLeader_in_output_list; eauto].
      match goal with
        | _ : doLeader ?st ?h = _, _ : doGenericServer _ ?d = _ |- _ =>
          replace st with ((update (nwState net) h st) h) in *;
            [|rewrite_update; auto]
      end.
      find_apply_lem_hyp doLeader_appliedEntries.
      rewrite_update. repeat find_rewrite_lem update_overwrite.
      unfold data in *. simpl in *.
      find_rewrite.
      match goal with
        | _ : raft_intermediate_reachable (mkNetwork ?ps ?st),
          H : doGenericServer ?h ?r = _ |- _ =>
          replace r with (nwState (mkNetwork ps st) h) in H by (simpl in *; rewrite_update; auto)
      end.
      find_eapply_lem_hyp doGenericServer_in_output_list; [|idtac|eauto]; eauto.
      break_exists_exists. intuition. simpl in *.
      find_rewrite_lem update_overwrite. auto.
  Qed.

  Instance TR : TraceRelation step_f :=
    {
      init := step_f_init;
      T := in_output ;
      T_dec := in_output_dec;
      R := fun s => in_applied_entries (snd s)
    }.
  Proof.
  - intros.
    unfold in_applied_entries in *.
    break_exists; eexists; intuition eauto.
    destruct s; destruct s'; eapply applied_entries_monotonic; eauto.
    eauto using refl_trans_1n_n1_trace, step_f_star_raft_intermediate_reachable.
  - unfold in_output in *. intuition.
    break_exists; intuition.
  - intros.
    destruct s as [failed net].
    destruct s' as [failed' net']. simpl in *.
    find_apply_lem_hyp step_f_star_raft_intermediate_reachable.
    find_apply_lem_hyp in_output_changed; auto.
    eauto using output_implies_in_applied_entries.
  Defined.

  Theorem output_implies_applied :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      in_output tr ->
      in_applied_entries net.
  Proof.
    intros. pose proof (trace_relations_work (failed, net) tr).
    concludes. intuition.
  Qed.
End OutputImpliesApplied.
