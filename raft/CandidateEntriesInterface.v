Require Import List.
Import ListNotations.

Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Export CommonDefinitions.
Require Export RefinementCommonDefinitions.

Section CandidateEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition candidateEntries_host_invariant sigma :=
    (forall h e, In e (log (snd (sigma h))) ->
                 candidateEntries e sigma).

  Definition candidateEntries_nw_invariant net :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      forall e,
        In e entries ->
        candidateEntries e (nwState net).

  Definition CandidateEntries net : Prop :=
    candidateEntries_host_invariant (nwState net) /\ candidateEntries_nw_invariant net.

  Class candidate_entries_interface : Prop :=
    {
      candidate_entries_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          CandidateEntries net
    }.
End CandidateEntriesInterface.
