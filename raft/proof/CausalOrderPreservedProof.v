Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import TraceRelations.
Require Import UpdateLemmas.

Require Import Raft.
Require Import CommonTheorems.

Require Import CausalOrderPreservedInterface.
Require Import OutputImpliesAppliedInterface.
Require Import AppliedImpliesInputInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section CausalOrderPreserved.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.
  Context {aiii : applied_implies_input_interface}.

  Section inner.
  Variables client id client' id' : nat.

  Instance TR : TraceRelation step_f :=
    {
      init := step_f_init;
      T := output_before_input client id client' id';
      R := fun s => entries_ordered client id client' id' (snd s)
    }.
  Proof.
    - admit.
    - admit.
    - admit.
    - admit.
  Defined.

  Theorem causal_order_preserved :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      output_before_input client id client' id' tr ->
      entries_ordered client id client' id' net.
  Proof.
    intros. pose proof (trace_relations_work (failed, net) tr).
    concludes. intuition.
  Qed.

  End inner.

  Instance copi : causal_order_preserved_interface.
  Proof.
    split.
    intros.
    eapply causal_order_preserved; eauto.
  Qed.
End CausalOrderPreserved.
