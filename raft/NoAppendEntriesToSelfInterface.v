Require Import Raft.
Require Import CommonDefinitions.

Section NoAppendEntriesToSelfInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition no_append_entries_to_self (net : network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      pDst p = pSrc p ->
      False.

  Class no_append_entries_to_self_interface : Prop :=
    {
      no_append_entries_to_self_invariant :
        forall net,
          raft_intermediate_reachable net ->
          no_append_entries_to_self net
    }.
End NoAppendEntriesToSelfInterface.
