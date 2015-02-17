Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import CommonTheorems.
Require Import Raft.

Section AppliedEntriesMonotonic.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem applied_entries_monotonic' :
    forall failed net failed' net' os,
      raft_intermediate_reachable net ->
      (@step_f _ _ failure_params (failed, net) (failed', net') os) ->
      exists es,
        applied_entries (nwState net') = applied_entries (nwState net) ++ es.
  Proof.
    (* proof should use State Machine Safety *) 
  Admitted.
  
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
