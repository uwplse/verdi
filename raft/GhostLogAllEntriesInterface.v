Require Import RaftState.
Require Import Raft.

Require Import RaftRefinementInterface.
Require Import RaftMsgRefinementInterface.

Section GhostLogAllEntriesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition ghost_log_allEntries net :=
    forall p e,
      In p (nwPackets net) ->
      In e (fst (pBody p)) ->
      exists t,
        In (t, e) (allEntries (fst (nwState net (pSrc p)))).


  Class ghost_log_allEntries_interface : Prop :=
    {
      ghost_log_allEntries_invariant :
        forall net,
          msg_refined_raft_intermediate_reachable net ->
          ghost_log_allEntries net
    }.
  
End GhostLogAllEntriesInterface.
