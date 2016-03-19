Require Import Raft.
Require Import CommonDefinitions.

Section NoAppendEntriesToLeaderInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition no_append_entries_to_leader (net : network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (nwState net (pDst p)) = Leader ->
      currentTerm (nwState net (pDst p)) = t ->
      False.

  Class no_append_entries_to_leader_interface : Prop :=
    {
      no_append_entries_to_leader_invariant :
        forall net,
          raft_intermediate_reachable net ->
          no_append_entries_to_leader net
    }.
End NoAppendEntriesToLeaderInterface.
