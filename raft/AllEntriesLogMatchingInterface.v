Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition allEntries_log_matching net :=
    forall e e' h h',
      In e (log (snd (nwState net h))) ->
      In e' (map snd (allEntries (fst (nwState net h')))) ->
      eTerm e = eTerm e' ->
      eIndex e = eIndex e' ->
      e = e'.

  Class allEntries_log_matching_interface : Prop :=
    {
      allEntries_log_matching_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          allEntries_log_matching net
    }.
End AllEntriesLogMatching.
