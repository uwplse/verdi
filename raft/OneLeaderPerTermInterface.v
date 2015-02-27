Require Import List.

Require Import Net.
Require Import Raft.

Section OneLeaderPerTermInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition one_leader_per_term (net : network) :=
    forall h h',
      currentTerm (nwState net h) = currentTerm (nwState net h') ->
      type (nwState net h) = Leader ->
      type (nwState net h') = Leader ->
      h = h'.

  Class one_leader_per_term_interface : Prop :=
    {
      one_leader_per_term_invariant :
        forall net,
          raft_intermediate_reachable net -> one_leader_per_term net
    }.
End OneLeaderPerTermInterface.