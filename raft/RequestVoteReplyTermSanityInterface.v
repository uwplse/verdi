Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section RequestVoteReplyTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition requestVoteReply_term_sanity (net : network) : Prop :=
    forall t p,
      In p (nwPackets net) ->
      pBody p = RequestVoteReply t true ->
      t <= currentTerm (snd (nwState net (pDst p))).

  Class requestVoteReply_term_sanity_interface : Prop :=
    {
      requestVoteReply_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          requestVoteReply_term_sanity net
    }.
End RequestVoteReplyTermSanity.
