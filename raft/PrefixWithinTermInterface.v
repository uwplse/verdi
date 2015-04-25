Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section PrefixWithinTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition allEntries_leaderLogs_prefix_within_term net :=
    forall h t l h',
      In (t, l) (leaderLogs (fst (nwState net h'))) ->
      prefix_within_term (map snd (allEntries (fst (nwState net h)))) l.

  Definition log_log_prefix_within_term net :=
    forall h h',
      prefix_within_term (log (snd (nwState net h))) (log (snd (nwState net h'))).


  Class prefix_within_term_interface : Prop :=
    {
      allEntries_leaderLogs_prefix_within_term_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_leaderLogs_prefix_within_term net;
      log_log_prefix_within_term_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          log_log_prefix_within_term net
    }.
End PrefixWithinTerm.
