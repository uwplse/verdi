Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesLog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  
  Definition allEntries_log (net : network) : Prop :=
    forall t e h,
      In (t, e) (allEntries (fst (nwState net h))) ->
      In e (log (snd (nwState net h))) \/
      (exists t' leader ll,
         In (t', ll) (leaderLogs (fst (nwState net leader))) /\
         t < t' <= currentTerm (snd (nwState net h)) /\
         ~ In e ll /\
         (leaderId (snd (nwState net h)) <> None
          \/ t' < currentTerm (snd (nwState net h)))).

  Class allEntries_log_interface : Prop :=
    {
      allEntries_log_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_log net
    }.
End AllEntriesLog.
