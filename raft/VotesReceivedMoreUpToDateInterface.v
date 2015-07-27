Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section VotesReceivedMoreUpToDate.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition votesReceived_moreUpToDate (net : network) : Prop :=
    forall t h h',
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Candidate ->
      In h' (votesReceived (snd (nwState net h))) ->
      exists vl,
        moreUpToDate (maxTerm (log (snd (nwState net h)))) (maxIndex (log (snd (nwState net h))))
                     (maxTerm vl) (maxIndex vl) = true /\
        In (t, h, vl) (votesWithLog (fst (nwState net h'))).

  Class votesReceived_moreUpToDate_interface : Prop :=
    {
      votesReceived_moreUpToDate_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          votesReceived_moreUpToDate net
    }.
End VotesReceivedMoreUpToDate.
