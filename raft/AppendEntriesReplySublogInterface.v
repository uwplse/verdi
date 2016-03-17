Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import Raft.

Section AppendEntriesReplySublog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition append_entries_reply_sublog net :=
    forall p t es h e,
      In p (nwPackets net) ->
      pBody p = AppendEntriesReply t es true ->
      currentTerm (nwState net h) = t ->
      type (nwState net h) = Leader ->
      In e es ->
      In e (log (nwState net h)).


  Class append_entries_reply_sublog_interface : Prop :=
    {
      append_entries_reply_sublog_invariant :
        forall net,
          raft_intermediate_reachable net ->
          append_entries_reply_sublog net
    }.
End AppendEntriesReplySublog.

