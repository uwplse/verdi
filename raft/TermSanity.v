Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.
Require Import CommonTheorems.

Section TermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  
  Definition no_entries_past_current_term_host net :=
    forall (h : name) e,
      In e (log (nwState net h)) ->
      eTerm e <= currentTerm (nwState net h).

  Definition no_entries_past_current_term_nw net :=
    forall e p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      In e entries ->
      eTerm e <= t.

  Definition no_entries_past_current_term net :=
    no_entries_past_current_term_host net /\
    no_entries_past_current_term_nw net.

  Theorem no_entries_past_current_term_invariant :
    forall net,
      raft_intermediate_reachable net ->
      no_entries_past_current_term net.
  Admitted.
End TermSanity.
