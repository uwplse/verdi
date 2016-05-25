Require Import Raft.

Section PrevLogLeaderSublogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition prevLog_leader_sublog (net : network) :=
    forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      type (nwState net leader) = Leader ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      currentTerm (nwState net leader) = prevLogTerm ->
      0 < prevLogIndex ->
      0 < prevLogTerm ->
      exists ple, eIndex ple = prevLogIndex /\
             eTerm ple = prevLogTerm /\
             In ple (log (nwState net leader)).

  Class prevLog_leader_sublog_interface : Prop :=
    {
      prevLog_leader_sublog_invariant :
        forall net,
          raft_intermediate_reachable net ->
          prevLog_leader_sublog net
    }.

End PrevLogLeaderSublogInterface.
