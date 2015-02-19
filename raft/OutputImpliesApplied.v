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
  
  Definition in_applied_entries (net : network) : Prop :=
    exists e,
      eClient e = client /\
      eId e = id /\
      In e (applied_entries (nwState net)).

  Lemma applied_entries'_log_lastApplied_same :
    forall sigma sigma' l,
      (forall h, lastApplied (sigma' h) = lastApplied (sigma h)) ->
      applied_entries' sigma' l = applied_entries' sigma l.
  Proof.
    intros. induction l; simpl in *; auto.
    repeat find_higher_order_rewrite. auto.
  Qed.
  
  Lemma applied_entries_log_lastApplied_same :
    forall sigma sigma',
      (forall h, log (sigma' h) = log (sigma h)) ->
      (forall h, lastApplied (sigma' h) = lastApplied (sigma h)) ->
      applied_entries sigma' = applied_entries sigma.
  Proof.
    intros.
    unfold applied_entries in *.
    erewrite applied_entries'_log_lastApplied_same; eauto.
    break_match; auto.
    break_let.
    find_higher_order_rewrite. auto.
  Qed.


  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.
  
  
  Lemma doLeader_appliedEntries :
  forall sigma h os st' ms,
    doLeader (sigma h) h = (os, st', ms) ->
    applied_entries (update sigma h st') = applied_entries sigma.
  Proof.
    intros.
    apply applied_entries_log_lastApplied_same.
    - intros. update_destruct; subst; rewrite_update; auto.
      eapply doLeader_same_log; eauto.
    - intros. update_destruct; subst; rewrite_update; auto.
      unfold doLeader in *. repeat break_match; find_inversion; auto.
  Qed.

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
    unfold applied_entries.

  
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
    admit.
  Defined.

  Theorem output_implies_applied :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      in_output tr ->
      in_applied_entries net.
  Proof.
    intros. pose proof (trace_relations_work step_f_init (failed, net) tr).
    concludes. intuition. find_apply_hyp_goal.
  Qed.
End OutputImpliesApplied.
