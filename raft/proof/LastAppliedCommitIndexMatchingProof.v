Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import CommonDefinitions.

Require Import LastAppliedCommitIndexMatchingInterface.
Require Import LogMatchingInterface.
Require Import StateMachineSafetyInterface.
Require Import MaxIndexSanityInterface.

Section LastAppliedCommitIndexMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lmi : log_matching_interface}.
  Context {smsi : state_machine_safety_interface}.
  Context {misi : max_index_sanity_interface}.

  Theorem lastApplied_commitIndex_match_invariant :
    forall net,
      raft_intermediate_reachable net ->
      lastApplied_commitIndex_match net.
  Proof.
    intros.
    find_copy_apply_lem_hyp log_matching_invariant. unfold log_matching in *.
    find_copy_apply_lem_hyp state_machine_safety_invariant. unfold state_machine_safety in *.
    find_copy_apply_lem_hyp max_index_sanity_invariant. unfold maxIndex_sanity in *.
    unfold lastApplied_commitIndex_match.
    intuition; simpl in *.
    - unfold log_matching_hosts in *. intuition. simpl in *.
      match goal with
        | H : forall (_ : name) (_ : nat), _ |- In ?e (_ (_ ?h)) =>
          specialize (H h (eIndex e)); forward H;
          intuition
      end.
      + find_apply_hyp_hyp; omega.
      + eapply le_trans; [|eapply_prop maxIndex_commitIndex].
        simpl. omega.
      + break_exists. intuition.
        match goal with
          | _ : eIndex ?e = eIndex ?e' |- _ =>
            cut (e = e'); [intros; subst; auto|]
        end.
        eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto;
        simpl in *; intuition.
    - unfold log_matching_hosts in *. intuition. simpl in *.
      match goal with
        | H : forall (_ : name) (_ : nat), _ |- In ?e (_ (_ ?h)) =>
          specialize (H h (eIndex e)); forward H;
          intuition
      end.
      + find_apply_hyp_hyp; omega.
      + eapply le_trans; [|eapply_prop maxIndex_lastApplied].
        simpl. omega.
      + break_exists. intuition.
        match goal with
          | _ : eIndex ?e = eIndex ?e' |- _ =>
            cut (e = e'); [intros; subst; auto|]
        end.
        eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto;
        simpl in *; intuition.
  Qed.

  Theorem commitIndex_lastApplied_match_invariant :
    forall net,
      raft_intermediate_reachable net ->
      commitIndex_lastApplied_match net.
  Proof.
    intros.
    find_copy_apply_lem_hyp log_matching_invariant. unfold log_matching in *.
    find_copy_apply_lem_hyp state_machine_safety_invariant. unfold state_machine_safety in *.
    find_copy_apply_lem_hyp max_index_sanity_invariant. unfold maxIndex_sanity in *.
    unfold commitIndex_lastApplied_match.
    intuition; simpl in *.
    - unfold log_matching_hosts in *. intuition. simpl in *.
      match goal with
        | H : forall (_ : name) (_ : nat), _ |- In ?e (_ (_ ?h)) =>
          specialize (H h (eIndex e)); forward H;
          intuition
      end.
      + find_apply_hyp_hyp; omega.
      + eapply le_trans; [|eapply_prop maxIndex_lastApplied].
        simpl. omega.
      + break_exists. intuition.
        match goal with
          | _ : eIndex ?e = eIndex ?e' |- _ =>
            cut (e = e'); [intros; subst; auto|]
        end.
        eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto;
        simpl in *; intuition.
    - unfold log_matching_hosts in *. intuition. simpl in *.
      match goal with
        | H : forall (_ : name) (_ : nat), _ |- In ?e (_ (_ ?h)) =>
          specialize (H h (eIndex e)); forward H;
          intuition
      end.
      + find_apply_hyp_hyp; omega.
      + eapply le_trans; [|eapply_prop maxIndex_commitIndex].
        simpl. omega.
      + break_exists. intuition.
        match goal with
          | _ : eIndex ?e = eIndex ?e' |- _ =>
            cut (e = e'); [intros; subst; auto|]
        end.
        eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto;
        simpl in *; intuition.
  Qed.
  
  Theorem lastApplied_lastApplied_match_invariant :
    forall net,
      raft_intermediate_reachable net ->
      lastApplied_lastApplied_match net.
  Proof.
    intros.
    find_copy_apply_lem_hyp log_matching_invariant. unfold log_matching in *.
    find_copy_apply_lem_hyp state_machine_safety_invariant. unfold state_machine_safety in *.
    find_copy_apply_lem_hyp max_index_sanity_invariant. unfold maxIndex_sanity in *.
    unfold lastApplied_lastApplied_match.
    intuition; simpl in *.
    - unfold log_matching_hosts in *. intuition. simpl in *.
      match goal with
        | H : forall (_ : name) (_ : nat), _ |- In ?e (_ (_ ?h)) =>
          specialize (H h (eIndex e)); forward H;
          intuition
      end.
      + find_apply_hyp_hyp; omega.
      + eapply le_trans; [|eapply_prop maxIndex_lastApplied].
        simpl. omega.
      + break_exists. intuition.
        match goal with
          | _ : eIndex ?e = eIndex ?e' |- _ =>
            cut (e = e'); [intros; subst; auto|]
        end.
        eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto;
        simpl in *; intuition.
    - unfold log_matching_hosts in *. intuition. simpl in *.
      match goal with
        | H : forall (_ : name) (_ : nat), _ |- In ?e (_ (_ ?h)) =>
          specialize (H h (eIndex e)); forward H;
          intuition
      end.
      + find_apply_hyp_hyp; omega.
      + eapply le_trans; [|eapply_prop maxIndex_lastApplied].
        simpl. omega.
      + break_exists. intuition.
        match goal with
          | _ : eIndex ?e = eIndex ?e' |- _ =>
            cut (e = e'); [intros; subst; auto|]
        end.
        eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto;
        simpl in *; intuition.
  Qed.

  Instance lacimi : lastApplied_commitIndex_match_interface.
  split.
  - exact lastApplied_commitIndex_match_invariant.
  - exact commitIndex_lastApplied_match_invariant.
  - exact lastApplied_lastApplied_match_invariant.
  Defined.
End LastAppliedCommitIndexMatching.
