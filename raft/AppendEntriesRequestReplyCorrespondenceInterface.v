Require Import Raft.


Section AppendEntriesRequestReplyCorrespondence.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition exists_equivalent_network_with_aer net from to t es :=
    exists net' pli plt ci n,
      raft_intermediate_reachable net' /\
      nwState net' = nwState net /\
      nwPackets net' = nwPackets net ++
                                 [ {| pSrc := from; pDst := to; pBody := AppendEntries t n pli plt es ci |} ].

  Definition append_entries_request_reply_correspondence net :=
    forall p t es,
      In p (nwPackets net) ->
      pBody p = AppendEntriesReply t es true ->
      exists_equivalent_network_with_aer net (pDst p) (pSrc p) t es.

  Class append_entries_request_reply_correspondence_interface : Prop :=
    {
      append_entries_request_reply_correspondence_invariant :
        forall net,
          raft_intermediate_reachable net ->
          append_entries_request_reply_correspondence net
    }.

    
End AppendEntriesRequestReplyCorrespondence.
