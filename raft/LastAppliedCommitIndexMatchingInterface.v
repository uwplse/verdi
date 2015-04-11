Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.

Section LastAppliedCommitIndexMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition lastApplied_commitIndex_match net :=
    forall h h' e,
      lastApplied (nwState net h') <= commitIndex (nwState net h) ->
      eIndex e <= lastApplied (nwState net h') ->
      In e (log (nwState net h')) <-> In e (log (nwState net h)).

  Definition commitIndex_lastApplied_match net :=
    forall h h' e,
      commitIndex (nwState net h') <= lastApplied (nwState net h) ->
      eIndex e <= commitIndex (nwState net h') ->
      In e (log (nwState net h')) <-> In e (log (nwState net h)).

  Definition lastApplied_lastApplied_match net :=
    forall h h' e,
      lastApplied (nwState net h') <= lastApplied (nwState net h) ->
      eIndex e <= lastApplied (nwState net h') ->
      In e (log (nwState net h')) <-> In e (log (nwState net h)).
  
  Class lastApplied_commitIndex_match_interface : Prop :=
    {
      lastApplied_commitIndex_match_invariant :
        forall net,
          raft_intermediate_reachable net ->
          lastApplied_commitIndex_match net;
      commitIndex_lastApplied_match_invariant :
        forall net,
          raft_intermediate_reachable net ->
          commitIndex_lastApplied_match net;
      lastApplied_lastApplied_match_invariant :
        forall net,
          raft_intermediate_reachable net ->
          lastApplied_lastApplied_match net
    }.
  
End LastAppliedCommitIndexMatching.
