Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section LeaderLogsVotesWithLog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition leaderLogs_votesWithLog (net : network) : Prop :=
    forall t ll leader,
      In (t, ll) (leaderLogs (fst (nwState net leader))) ->
      exists quorum,
        NoDup quorum /\
        length quorum > div2 (length nodes) /\
        forall h, In h quorum ->
                  exists log,
                    moreUpToDate (maxTerm ll) (maxIndex ll) (maxTerm log) (maxIndex log) = true /\
                    In (t, leader, log) (votesWithLog (fst (nwState net h))).

  Class leaderLogs_votesWithLog_interface : Prop :=
    {
      leaderLogs_votesWithLog_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leaderLogs_votesWithLog net
    }.
End LeaderLogsVotesWithLog.