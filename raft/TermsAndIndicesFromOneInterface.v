Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section TermsAndIndicesFromOne.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition terms_and_indices_from_one (l : list entry) : Prop :=
    forall e,
      In e l ->
      eTerm e >= 1 /\ eIndex e >= 1.

  Class terms_and_indices_from_one_interface : Prop :=
    {
      terms_and_indices_from_one_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          forall h t h' log,
            In (t, h', log) (votesWithLog (fst (nwState net h))) ->
            terms_and_indices_from_one log
    }.
End TermsAndIndicesFromOne.