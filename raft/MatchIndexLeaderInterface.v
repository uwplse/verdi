Require Import Raft.

Section MatchIndexLeader.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition match_index_leader net :=
    forall leader,
      type (nwState net leader) = Leader ->
      assoc_default name_eq_dec (matchIndex (nwState net leader)) leader 0 = 
      maxIndex (log (nwState net leader)).

  Class match_index_leader_interface : Prop :=
    {
      match_index_leader_invariant :
        forall net,
          raft_intermediate_reachable net ->
          match_index_leader net
    }.
  
End MatchIndexLeader.
