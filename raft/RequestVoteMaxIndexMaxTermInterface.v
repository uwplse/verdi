Require Import Raft.
Require Import RaftRefinementInterface.

Section RequestVoteMaxIndexMaxTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition requestVote_maxIndex_maxTerm (net : network) : Prop :=
    forall t h p n mi mt,
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Candidate ->
      In p (nwPackets net) ->
      pBody p = RequestVote t n mi mt ->
      pSrc p = h ->
      maxIndex (log (snd (nwState net h))) = mi /\
      maxTerm (log (snd (nwState net h))) = mt.

  Class requestVote_maxIndex_maxTerm_interface : Prop :=
    {
      requestVote_maxIndex_maxTerm_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          requestVote_maxIndex_maxTerm net
    }.
End RequestVoteMaxIndexMaxTerm.
