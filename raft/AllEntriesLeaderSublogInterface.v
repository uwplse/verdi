Require Import List.

Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesLeaderSublogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition allEntries_leader_sublog (net : network) :=
    forall leader e h,
      type (snd (nwState net leader)) = Leader ->
      In e (map snd (allEntries (fst (nwState net h)))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).

  Class allEntries_leader_sublog_interface : Prop :=
    {
      allEntries_leader_sublog_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_leader_sublog net
    }.

End AllEntriesLeaderSublogInterface.
