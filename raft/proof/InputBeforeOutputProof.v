Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import InverseTraceRelations.
Require Import UpdateLemmas.

Require Import Raft.
Require Import CommonTheorems.
Require Import TraceUtil.

Require Import InputBeforeOutputInterface.
Require Import AppliedImpliesInputInterface.
Require Import OutputImpliesAppliedInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section InputBeforeOutput.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.
  Context {aiii : applied_implies_input_interface}.

  Section inner.
  Variables client id : nat.

  Instance TR : InverseTraceRelation step_f :=
    {
      init := step_f_init;
      T := input_before_output client id;
      R := fun s => in_applied_entries client id (snd s) 
    }.
  Proof.
    - admit.
    - admit.
    - admit.
    - admit.
  Defined.

  Theorem output_implies_input_before_output :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      key_in_output_trace client id tr ->
      input_before_output client id tr.
  Proof.
    intros. pose proof (inverse_trace_relations_work (failed, net) tr).
    concludes.
    find_eapply_lem_hyp output_implies_applied; eauto.
    intuition.
  Qed.

  End inner.

  Instance iboi : input_before_output_interface.
  Proof.
    split.
    intros.
    eapply output_implies_input_before_output; eauto.
  Qed.
End InputBeforeOutput.
