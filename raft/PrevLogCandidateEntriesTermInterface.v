Require Import Raft.
Require Import RaftRefinementInterface.
Require Import RefinementCommonDefinitions.

Section PrevLogCandidateEntriesTermInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition prevLog_candidateEntriesTerm (net : network) :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      0 < prevLogTerm ->
      candidateEntriesTerm prevLogTerm (nwState net).

  Class prevLog_candidateEntriesTerm_interface : Prop :=
    {
      prevLog_candidateEntriesTerm_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          prevLog_candidateEntriesTerm net
    }.
End PrevLogCandidateEntriesTermInterface.
