Require Import Raft.

Require Import CommonDefinitions.

Section UniqueIndicesInterface.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition uniqueIndices_host_invariant net :=
    (forall h, uniqueIndices (log (nwState net h))).

  Definition uniqueIndices_nw_invariant net :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      uniqueIndices entries.
    
  Definition UniqueIndices net : Prop :=
    uniqueIndices_host_invariant net /\ uniqueIndices_nw_invariant net.

  Class unique_indices_interface : Prop := 
    { 
      UniqueIndices_invariant :
        forall net,
          raft_intermediate_reachable net ->
          UniqueIndices net
    }.
End UniqueIndicesInterface.
