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
Require Import OutputImpliesApplied.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section AppliedImpliesInput.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Variables client id : nat.

  Definition in_input (tr : list (name * (raft_input + list raft_output))) : Prop :=
    exists h i,
      In (h, inl (ClientRequest client id i)) tr.

  Lemma applied_implies_input :
    forall failed net tr e,
      step_f_star step_f_init (failed, net) tr ->
      eClient e = client ->
      eId e = id ->
      In e (applied_entries (nwState net)) ->
      in_input tr.
  Admitted.
End AppliedImpliesInput.
