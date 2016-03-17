Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import Raft.
Require Import RaftRefinementInterface.

Section LogAllEntries.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition log_all_entries net :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      In (eTerm e, e) (allEntries (fst (nwState net h))).

  Class log_all_entries_interface : Prop :=
    {
      log_all_entries_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          log_all_entries net
    }.
End LogAllEntries.
