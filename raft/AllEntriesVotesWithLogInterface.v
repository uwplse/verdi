Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesVotesWithLog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition allEntries_votesWithLog (net : network) : Prop :=
    forall t e t' leader h log,
      In (t, e) (allEntries (fst (nwState net h))) ->
      In (t', leader, log) (votesWithLog (fst (nwState net h))) ->
      t < t' ->
      In e log \/
      (exists t'' leader' log',
         In (t'', log') (leaderLogs (fst (nwState net leader'))) /\
         t < t'' < t' /\
         ~ In e log').

  Class allEntries_votesWithLog_interface : Prop :=
    {
      allEntries_votesWithLog_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_votesWithLog net
    }.
End AllEntriesVotesWithLog.
