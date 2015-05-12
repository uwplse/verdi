Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.

Section OneLeaderLogPerTerm.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition one_leaderLog_per_term (net : network) : Prop :=
    forall h h' t ll ll',
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In (t, ll') (leaderLogs (fst (nwState net h'))) ->
      h = h' /\ ll = ll'.

  (* convenience *)
  Definition one_leaderLog_per_term_log (net : network) : Prop :=
    forall h h' t ll ll',
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In (t, ll') (leaderLogs (fst (nwState net h'))) ->
      ll = ll'.

  (* convenience *)
  Definition one_leaderLog_per_term_host (net : network) : Prop :=
    forall h h' t ll ll',
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In (t, ll') (leaderLogs (fst (nwState net h'))) ->
      h = h'.


  Class one_leaderLog_per_term_interface : Prop :=
    {
      one_leaderLog_per_term_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          one_leaderLog_per_term net;
      one_leaderLog_per_term_log_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          one_leaderLog_per_term_log net;
      one_leaderLog_per_term_host_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          one_leaderLog_per_term net
    }.
End OneLeaderLogPerTerm.
