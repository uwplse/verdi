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

  Lemma maxIndex_sanity_init :
    raft_net_invariant_init maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_client_request :
    raft_net_invariant_client_request maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_timeout :
    raft_net_invariant_timeout maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_append_entries :
    raft_net_invariant_append_entries maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_append_entries_reply :
    raft_net_invariant_append_entries_reply maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_request_vote :
    raft_net_invariant_request_vote maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_request_vote_reply :
    raft_net_invariant_request_vote_reply maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_do_leader :
    raft_net_invariant_do_leader maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_do_generic_server :
    raft_net_invariant_do_generic_server maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_reboot :
    raft_net_invariant_reboot maxIndex_sanity.
  Admitted.

  Lemma maxIndex_sanity_invariant :
    forall net,
      raft_intermediate_reachable net ->
      maxIndex_sanity net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply maxIndex_sanity_init.
    - apply maxIndex_sanity_client_request.
    - apply maxIndex_sanity_timeout.
    - apply maxIndex_sanity_append_entries.
    - apply maxIndex_sanity_append_entries_reply.
    - apply maxIndex_sanity_request_vote.
    - apply maxIndex_sanity_request_vote_reply.
    - apply maxIndex_sanity_do_leader.
    - apply maxIndex_sanity_do_generic_server.
    - apply maxIndex_sanity_state_same_packet_subset.
    - apply maxIndex_sanity_reboot.
  Qed.

  Instance misi : max_index_sanity_interface.
  Proof.
    split.
    exact maxIndex_sanity_invariant.
  Qed.
End MaxIndexSanity.