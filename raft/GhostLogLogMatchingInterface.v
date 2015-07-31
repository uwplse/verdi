Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftMsgRefinementInterface.

Require Import CommonDefinitions.

Section GhostLogLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition ghost_log_entries_match_host (net : network) : Prop :=
    forall h p,
      In p (nwPackets net) ->
      entries_match (log (snd (nwState net h))) (fst (pBody p)).

  Class ghost_log_entries_match_interface : Prop :=
    {
      ghost_log_entries_match_invariant :
        forall net,
          msg_refined_raft_intermediate_reachable net ->
          ghost_log_entries_match_host net
    }.
  
End GhostLogLogMatching.
