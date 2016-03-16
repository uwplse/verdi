Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section VotesVotesWithLogCorrespond.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition votes_votesWithLog (net : network) : Prop :=
    forall h t h' log,
      In (t, h', log) (votesWithLog (fst (nwState net h))) ->
      In (t, h') (votes (fst (nwState net h))).

  Definition votesWithLog_votes (net : network) : Prop :=
    forall h t h',
      In (t, h') (votes (fst (nwState net h))) ->
      exists log, In (t, h', log) (votesWithLog (fst (nwState net h))).

  Definition votes_votesWithLog_correspond (net : network) : Prop :=
    votes_votesWithLog net /\ votesWithLog_votes net.

  Class votes_votesWithLog_correspond_interface : Prop :=
    {
      votes_votesWithLog_correspond_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          votes_votesWithLog_correspond net
    }.
End VotesVotesWithLogCorrespond.
