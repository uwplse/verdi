Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section PrefixWithinTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.



  Class prefix_within_term_interface : Prop :=
    {
      prefix_within_term_invariant :
        forall net h t l h',
          In (t, l) (leaderLogs (fst (nwState net h'))) ->
          prefix_within_term (map snd (allEntries (fst (nwState net h)))) l
    }.
End PrefixWithinTerm.
