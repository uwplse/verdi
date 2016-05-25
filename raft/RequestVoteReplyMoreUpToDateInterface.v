Require Import Raft.
Require Import RaftRefinementInterface.

Section RequestVoteReplyMoreUpToDate.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition requestVoteReply_moreUpToDate (net : network) : Prop :=
    forall t h h' p,
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Candidate ->
      In p (nwPackets net) ->
      pBody p = RequestVoteReply t true ->
      pDst p = h ->
      pSrc p = h' ->
      exists vl,
        moreUpToDate (maxTerm (log (snd (nwState net h)))) (maxIndex (log (snd (nwState net h))))
                     (maxTerm vl) (maxIndex vl) = true /\
        In (t, h, vl) (votesWithLog (fst (nwState net h'))).

  Class requestVoteReply_moreUpToDate_interface : Prop :=
    {
      requestVoteReply_moreUpToDate_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          requestVoteReply_moreUpToDate net
    }.
End RequestVoteReplyMoreUpToDate.
