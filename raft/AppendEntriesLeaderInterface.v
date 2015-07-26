Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition appendEntries_leader net :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit h e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      In e entries ->
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Leader ->
      In e (log (snd (nwState net h))).


  Class append_entries_leaders_interface : Prop :=
    {
      append_entries_leaders_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          appendEntries_leader net
    }.
End AllEntriesLeaderLogs.
