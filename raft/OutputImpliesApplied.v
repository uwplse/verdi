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
        
  Definition in_applied_entries (net : network) : Prop :=
    exists e,
      eClient e = client /\
      eId e = id /\
      In e (applied_entries (nwState net)).

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
