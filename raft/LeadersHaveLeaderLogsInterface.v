Require Import List.
Import ListNotations.

Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.

Section LeadersHaveLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaders_have_leaderLogs net :=
    forall h,
      type (snd (nwState net h)) = Leader ->
      exists ll,
        In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))).

  Class leaders_have_leaderLogs_interface : Prop :=
    {
      leaders_have_leaderLogs_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          leaders_have_leaderLogs net
    }.
End LeadersHaveLeaderLogs.
