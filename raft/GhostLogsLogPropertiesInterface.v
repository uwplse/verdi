Require Import Raft.
Require Import RaftMsgRefinementInterface.

Section GhostLogsLogProperties.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  
  Definition msg_log_property (P : list entry -> Prop) :=
    forall net h,
      msg_refined_raft_intermediate_reachable net ->
      P (log (snd (nwState net h))).
    
  Definition log_properties_hold_on_ghost_logs net :=
    forall P p,
      msg_log_property P ->
      In p (nwPackets net) ->
      P (fst (pBody p)).

  Class log_properties_hold_on_ghost_logs_interface : Prop :=
    {
      log_properties_hold_on_ghost_logs_invariant :
        forall (net : network),
          msg_refined_raft_intermediate_reachable net ->
          log_properties_hold_on_ghost_logs net
    }.
        
End GhostLogsLogProperties.
