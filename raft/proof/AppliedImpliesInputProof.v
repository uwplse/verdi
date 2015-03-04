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
Require Import TraceUtil.
Require Import OutputImpliesAppliedInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AppliedImpliesInputInterface.

Section AppliedImpliesInputProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.

  Section inner.
    Variables client id : nat.

    Lemma applied_implies_input :
      forall failed net tr e,
        step_f_star step_f_init (failed, net) tr ->
        eClient e = client ->
        eId e = id ->
        In e (applied_entries (nwState net)) ->
        in_input_trace client id (eInput e) tr.
    Admitted.
  End inner.

  Instance aiii : applied_implies_input_interface.
  Proof.
    split.
    exact applied_implies_input.
  Qed.
End AppliedImpliesInputProof.
