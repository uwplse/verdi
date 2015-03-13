Require Import List.
Import ListNotations.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import CommonDefinitions.

Require Import Raft.

Require Import MaxIndexSanityInterface.

Section MaxIndexSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem max_index_sanity_invariant : 
    forall net, 
      raft_intermediate_reachable net -> 
      maxIndex_sanity net.
  Admitted.

  Instance misi : max_index_sanity_interface.
  Proof.
    split.
    exact max_index_sanity_invariant.
  Qed.
End MaxIndexSanity.