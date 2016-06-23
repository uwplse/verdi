Require Import Raft.

Section LeaderSublogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leader_sublog_host_invariant (net : network) :=
    forall leader e h,
      type (nwState net leader) = Leader ->
      In e (log (nwState net h)) ->
      eTerm e = currentTerm (nwState net leader) ->
      In e (log (nwState net leader)).

  Definition leader_sublog_nw_invariant (net : network) :=
    forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
      type (nwState net leader) = Leader ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      In e entries ->
      eTerm e = currentTerm (nwState net leader) ->
      In e (log (nwState net leader)).

  Definition leader_sublog_invariant (net : network) :=
    leader_sublog_host_invariant net /\
    leader_sublog_nw_invariant net.

  Class leader_sublog_interface : Prop :=
    {
      leader_sublog_invariant_invariant :
        forall net,
          raft_intermediate_reachable net ->
          leader_sublog_invariant net
    }.

End LeaderSublogInterface.
