Require Import List.
Import ListNotations.

Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import RefinementCommonDefinitions.

Section CandidateEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_candidateEntries net :=
    (forall h e t ll,
       In (t, ll) (leaderLogs (fst (nwState net h))) ->
       In e ll ->
       candidateEntries e (nwState net)).

  Class leaderLogs_candidate_entries_interface : Prop :=
    {
      leaderLogs_candidate_entries_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          leaderLogs_candidateEntries net
    }.
End CandidateEntriesInterface.
