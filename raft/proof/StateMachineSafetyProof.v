Require Import List.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import StateMachineSafetyInterface.

Section StateMachineSafetyProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Definition lifted_state_machine_safety (net : network) : Prop :=
    state_machine_safety (deghost net).

  Lemma state_machine_safety_init :
    refined_raft_net_invariant_init lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_client_request :
    refined_raft_net_invariant_client_request lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_timeout :
    refined_raft_net_invariant_timeout lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_append_entries :
    refined_raft_net_invariant_append_entries lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_request_vote :
    refined_raft_net_invariant_request_vote lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_do_leader :
    refined_raft_net_invariant_do_leader lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_do_generic_server :
    refined_raft_net_invariant_do_generic_server lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_reboot :
    refined_raft_net_invariant_reboot lifted_state_machine_safety.
  Admitted.

  Lemma state_machine_safety_invariant' :
    forall net,
      refined_raft_intermediate_reachable net ->
      lifted_state_machine_safety net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply state_machine_safety_init.
    - apply state_machine_safety_client_request.
    - apply state_machine_safety_timeout.
    - apply state_machine_safety_append_entries.
    - apply state_machine_safety_append_entries_reply.
    - apply state_machine_safety_request_vote.
    - apply state_machine_safety_request_vote_reply.
    - apply state_machine_safety_do_leader.
    - apply state_machine_safety_do_generic_server.
    - apply state_machine_safety_state_same_packet_subset.
    - apply state_machine_safety_reboot.
  Qed.

  Theorem state_machine_safety_invariant :
    forall net,
      raft_intermediate_reachable net ->
      state_machine_safety net.
  Proof.
    apply lower_prop.
    intros.
    apply state_machine_safety_invariant' in H.
    auto.
  Qed.

  Instance smsi : state_machine_safety_interface.
  Proof.
    split.
    exact state_machine_safety_invariant.
  Qed.
End StateMachineSafetyProof.