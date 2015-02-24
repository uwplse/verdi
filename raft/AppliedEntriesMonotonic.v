Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.


Require Import Raft.
Require Import CommonTheorems.
Require Import StateMachineSafety.
Require Import Sorted.
Require Import UniqueIndices.
Require Import LogMatching.

Section AppliedEntriesMonotonic.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Theorem handleAppendEntries_log :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      log st' = log st \/
      (pli = 0 /\ t >= currentTerm st /\ log st' = es) \/
      (exists e,
         In e (log st) /\
         eIndex e = pli /\
         eTerm e = plt) /\
      t >= currentTerm st /\
      log st' = es ++ (removeAfterIndex (log st) pli).
  Proof.
    intros. unfold handleAppendEntries in *.
    break_if; [find_inversion; subst; eauto|].
    break_if; [find_inversion; subst; do_bool; eauto|].
    break_match; [|find_inversion; subst; eauto].
    break_if; [find_inversion; subst; eauto|].
    find_inversion; subst; simpl in *.
    right. right.
    find_apply_lem_hyp findAtIndex_elim.
    intuition; do_bool; eauto.
  Qed.

  Lemma sorted_NoDup :
    forall l,
      sorted l -> NoDup l.
  Proof.
    induction l; intros; simpl in *; auto.
    - constructor.
    - constructor; intuition.
      match goal with
        | H : forall _, _ |- _ => specialize (H a)
      end. intuition.
  Qed.

  Lemma removeAfterIndex_same_sufficient :
    forall x l l',
      sorted l ->
      sorted l' ->
      (forall e, eIndex e <= x ->
            In e l ->
            In e l') ->
      (forall e, eIndex e <= x ->
            In e l' ->
            In e l) ->
      removeAfterIndex l' x = removeAfterIndex l x.
  Proof.
    intros.
    admit.
  Qed.


  Ltac copy_eapply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    copy_eapply H H'
  end.

  
  Lemma handleMessage_applied_entries :
    forall net h h' m st' ms,
      raft_intermediate_reachable net ->
      In {| pBody := m; pDst := h; pSrc := h' |} (nwPackets net) ->
      handleMessage h' h m (nwState net h) = (st', ms) ->
      applied_entries (nwState net) = applied_entries (update (nwState net) h st').
  Proof.
    intros. symmetry.
    unfold handleMessage in *. break_match; repeat break_let; repeat find_inversion.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleRequestVote_same_log, handleRequestVote_same_lastApplied.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleRequestVoteReply_same_log, handleRequestVoteReply_same_lastApplied.
    - find_copy_eapply_lem_hyp handleAppendEntries_logs_sorted;
      eauto using logs_sorted_invariant.
      apply applied_entries_safe_update; eauto using handleAppendEntries_same_lastApplied.
      find_apply_lem_hyp handleAppendEntries_log. intuition.
      + repeat find_rewrite. auto.
      + subst.
        find_copy_apply_lem_hyp state_machine_safety_invariant.
        unfold state_machine_safety in *. intuition.
        find_copy_apply_lem_hyp logs_sorted_invariant.
        unfold logs_sorted in *. intuition.
        apply removeAfterIndex_same_sufficient; eauto.
        * intros. 
          eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *;
            simpl in *; repeat (forwards; eauto; concludes).
          intuition; omega.
        * intros.
          find_copy_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_hosts in *. intuition.
          match goal with
            | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (eIndex e));
                forward H
          end;
            copy_eapply_prop_hyp log_matching_nw AppendEntries; eauto;
            repeat (forwards; [intuition eauto; omega|]; concludes);
            intuition; [eapply le_trans; eauto|].
          match goal with
            | H : exists _, _ |- _ => destruct H as [e']
          end.
          intuition.
          copy_eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *;
            simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
          match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
          intuition; [omega|].
          find_copy_apply_lem_hyp UniqueIndices_invariant.
          unfold UniqueIndices in *. intuition.
          eapply rachet; [symmetry|idtac|idtac|idtac|idtac]; eauto.
      + repeat find_rewrite.
        find_copy_apply_lem_hyp state_machine_safety_invariant.
        unfold state_machine_safety in *. intuition.
        find_copy_apply_lem_hyp logs_sorted_invariant.
        unfold logs_sorted in *. intuition.
        apply removeAfterIndex_same_sufficient; eauto.
        * intros. 
          copy_eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *;
            simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
          match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
          intuition.
          apply in_or_app; right.
          apply removeAfterIndex_le_In; intuition.
        * intros.
          find_apply_lem_hyp in_app_iff. intuition eauto using removeAfterIndex_in.
          find_copy_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_hosts in *. intuition.
          match goal with
            | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (eIndex e));
                forward H
          end;
            copy_eapply_prop_hyp log_matching_nw AppendEntries; eauto;
            repeat (forwards; [simpl in *; intuition eauto; omega|]; concludes); break_and;
            match goal with
              | H : forall _, In _ _ -> _ < _ |- _ => specialize (H e)
            end; intuition;
            intuition; [eapply le_trans; eauto|].
          match goal with
            | H : exists _, _ |- _ => destruct H as [e']
          end.
          intuition.
          copy_eapply_prop_hyp state_machine_safety_nw In;
            unfold commit_recorded in *;
            simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
          match goal with H : _ /\ (_ \/ _) |- _ => clear H end. clean.
          intuition; [omega|].
          find_copy_apply_lem_hyp UniqueIndices_invariant.
          unfold UniqueIndices in *. intuition.
          eapply rachet; [symmetry|idtac|idtac|idtac|idtac]; eauto.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleAppendEntriesReply_same_log, handleAppendEntriesReply_same_lastApplied.
  Qed.

  Theorem handleTimeout_lastApplied :
    forall h st out st' ps,
      handleTimeout h st = (out, st', ps) ->
      lastApplied st' = lastApplied st.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; find_inversion; subst; auto.
  Qed.

  Theorem handleClientRequest_lastApplied:
  forall h st client id c out st' ps,
    handleClientRequest h st client id c = (out, st', ps) ->
    lastApplied st' = lastApplied st.
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; auto.
  Qed.

  
  Lemma handleInput_applied_entries :
    forall net h inp os st' ms,
      raft_intermediate_reachable net ->
      handleInput h inp (nwState net h) = (os, st', ms) ->
      applied_entries (nwState net) = applied_entries (update (nwState net) h st').
  Proof.
    intros. symmetry.
    unfold handleInput in *. break_match; repeat break_let; repeat find_inversion.
    - apply applied_entries_log_lastApplied_update_same;
      eauto using handleTimeout_log, handleTimeout_lastApplied.
    - apply applied_entries_safe_update; eauto using handleClientRequest_lastApplied.
      find_apply_lem_hyp handleClientRequest_log. intuition; repeat find_rewrite; eauto.
      break_exists. intuition. repeat find_rewrite.
      simpl in *. break_if; auto.
      exfalso.
      do_bool.
      find_apply_lem_hyp state_machine_safety_invariant.
      unfold state_machine_safety in *.
      intuition.
      unfold maxIndex_lastApplied in *.
      match goal with
        | H : forall _, _ |- _ => specialize (H h)
      end. omega.
  Qed.
  
  Lemma doGenericServer_applied_entries :
    forall ps h sigma os st' ms,
      raft_intermediate_reachable (mkNetwork ps sigma) ->
      doGenericServer h (sigma h) = (os, st', ms) ->
      exists es, applied_entries (update sigma h st') = (applied_entries sigma) ++ es.
  Proof.
  Admitted.


  Theorem applied_entries_monotonic' :
    forall failed net failed' net' os,
      raft_intermediate_reachable net ->
      (@step_f _ _ failure_params (failed, net) (failed', net') os) ->
      exists es,
        applied_entries (nwState net') = applied_entries (nwState net) ++ es.
  Proof.
    intros. match goal with H : step_f _ _ _ |- _ => invcs H end.
    - unfold RaftNetHandler in *. repeat break_let. subst.
      find_inversion.
      match goal with
        | Hdgs : doGenericServer ?h ?st = _,
          Hdl : doLeader ?st' ?h = _ |- context [update (nwState ?net) ?h ?st''] =>
          replace st with (update (nwState net) h st h) in Hdgs by eauto using update_eq;
            replace st' with (update (update (nwState net) h st) h st' h) in Hdl by eauto using update_eq;
            let H := fresh "H" in
            assert (update (nwState net) h st'' =
                    update (update (update (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H
      end.
      find_apply_lem_hyp doLeader_appliedEntries. find_rewrite.
      find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
      find_apply_lem_hyp handleMessage_applied_entries; auto; [|destruct p; find_rewrite; in_crush].
      find_rewrite.
      repeat match goal with H : applied_entries _ = applied_entries _ |- _ => clear H end.
      eauto using doGenericServer_applied_entries.
    - unfold RaftInputHandler in *. repeat break_let. subst.
      find_inversion.
      match goal with
        | Hdgs : doGenericServer ?h ?st = _,
          Hdl : doLeader ?st' ?h = _ |- context [update (nwState ?net) ?h ?st''] =>
          replace st with (update (nwState net) h st h) in Hdgs by eauto using update_eq;
            replace st' with (update (update (nwState net) h st) h st' h) in Hdl by eauto using update_eq;
            let H := fresh "H" in
            assert (update (nwState net) h st'' =
                    update (update (update (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H
      end.
      find_apply_lem_hyp doLeader_appliedEntries. find_rewrite.
      find_copy_eapply_lem_hyp RIR_handleInput; eauto.
      find_apply_lem_hyp handleInput_applied_entries; auto.
      find_rewrite.
      repeat match goal with H : applied_entries _ = applied_entries _ |- _ => clear H end.
      eauto using doGenericServer_applied_entries.
    - exists nil; intuition.
    - exists nil; intuition.
    - exists nil; intuition.
    - exists nil.
      rewrite app_nil_r.
      apply applied_entries_log_lastApplied_same;
        intros; unfold reboot in *; break_if; simpl; auto.
  Qed.
  
  Theorem applied_entries_monotonic :
    forall e failed net failed' net' os,
      raft_intermediate_reachable net ->
      (@step_f _ _ failure_params (failed, net) (failed', net') os) ->
      In e (applied_entries (nwState net)) ->
      In e (applied_entries (nwState net')).
  Proof.
    intros. find_eapply_lem_hyp applied_entries_monotonic'; eauto.
    break_exists. find_rewrite. in_crush.
  Qed.
  
End AppliedEntriesMonotonic.
