Require Import Raft.
Require Import RaftRefinementInterface.

Section LeadersHaveLeaderLogsStrong.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaders_have_leaderLogs_strong net :=
    forall h,
      type (snd (nwState net h)) = Leader ->
      exists ll es,
        In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))) /\
        log (snd (nwState net h)) = es ++ ll /\
        (forall e : entry, In e es -> eTerm e = currentTerm (snd (nwState net h))).
        

  Class leaders_have_leaderLogs_strong_interface : Prop :=
    {
      leaders_have_leaderLogs_strong_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          leaders_have_leaderLogs_strong net
    }.
End LeadersHaveLeaderLogsStrong.
