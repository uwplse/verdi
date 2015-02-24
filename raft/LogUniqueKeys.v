Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.
Require Import Permutation.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import TraceRelations.

Require Import Raft.
Require Import CommonTheorems.
Require Import RaftLinearizableDefinitions.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section LogUniqueKeys.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition eKey (e : entry) : nat * nat := (eClient e, eId e).

  Definition correspond_trace
             (es : list entry)
             (tr : list (name * (raft_input + list raft_output))) : Prop :=
    (forall k, In k (map eKey es) -> In k (project_input_keys tr)).

  Definition relate_logs (es es' : list entry) : Prop :=
    forall e e',
      eKey e = eKey e' ->
      In e es ->
      In e' es' ->
      eIndex e = eIndex e'.

  Definition unique_keys_host (net : network) tr : Prop :=
    (forall h, correspond_trace (log (nwState net h)) tr) /\
    (forall h h', relate_logs (log (nwState net h)) (log (nwState net h'))).

  Definition unique_keys_nw (net : network) tr : Prop :=
    (forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      correspond_trace entries tr) /\
    (forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      forall h,
        relate_logs entries (log (nwState net h))).

  Definition unique_keys_invariant (net : network) tr : Prop :=
    unique_keys_host net tr /\ unique_keys_nw net tr.

  Lemma unique_keys_init :
    unique_keys_invariant step_m_init [].
  Admitted.


  Lemma unique_keys_invariant_invariant :
    forall failed net tr,
      input_correct tr ->
      step_f_star step_f_init (failed, net) tr ->
      unique_keys_invariant net tr.
  Proof.
    intros.
    eapply state_trace_invariant_invariant with (R := unique_keys_invariant)
                                                (trace_wf := input_correct); eauto.
    - admit.
    - admit.
  Qed.
End LogUniqueKeys.
