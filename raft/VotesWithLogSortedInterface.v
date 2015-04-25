Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Section VotesWithLogSorted.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition votesWithLog_sorted (net : network) : Prop :=
    forall h t h' log, 
      In (t, h', log) (votesWithLog (fst (nwState net h))) -> 
      sorted log.

  Class votesWithLog_sorted_interface : Prop :=
    { 
      votesWithLog_sorted_invariant : 
        forall net, 
          refined_raft_intermediate_reachable net -> 
          votesWithLog_sorted net
    }.
End VotesWithLogSorted.
      