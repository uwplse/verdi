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

  Definition allEntries_candidateEntries net :=
    (forall h t e,
       In (t, e) (allEntries (fst (nwState net h))) ->
       candidateEntries e (nwState net)).

  Class allEntries_candidate_entries_interface : Prop :=
    {
      allEntries_candidateEntries_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          allEntries_candidateEntries net
    }.

End CandidateEntriesInterface.
