Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.
Require Import GhostSimulations.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import SortedInterface.
Require Import AppendEntriesRequestTermSanityInterface.

Section AppendEntriesRequestTermSanity.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {si : sorted_interface}.

  Theorem lift_sorted :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_sorted (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using logs_sorted_invariant.
  Qed.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof.
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma logs_sorted_aerts :
    forall net,
      logs_sorted (deghost net) ->
      append_entries_request_term_sanity net.
  Proof.
    unfold logs_sorted, append_entries_request_term_sanity. intuition.
    unfold packets_ge_prevTerm in *. find_apply_lem_hyp ghost_packet.
    eauto.
  Qed.

  Instance aertsi : append_entries_request_term_sanity_interface.
  Proof.
    split. intros. find_apply_lem_hyp lift_sorted.
    eauto using logs_sorted_aerts.
  Qed.
End AppendEntriesRequestTermSanity.
