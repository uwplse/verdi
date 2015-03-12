Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section LeaderLogsTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_term_sanity (net : network) : Prop:=
    forall h t log e,
      In (t, log) (leaderLogs (fst (nwState net h))) ->
      In e log ->
      eTerm e < t.

  Class leaderLogs_term_sanity_interface : Prop :=
    {
      leaderLogs_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leaderLogs_term_sanity net
    }.
End LeaderLogsTermSanity.
