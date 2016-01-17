Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import GhostSimulations.
Require Import VerdiTactics.
Require Import Raft.

Require Import CommonTheorems.

Require Import RaftRefinementInterface.
Require Import CroniesCorrectInterface.
Require Import VotesCorrectInterface.

Require Import OneLeaderPerTermInterface.

Section OneLeaderPerTermProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Ltac copy_eapply_prop_hyp P H :=
    match goal with
      | H' : P _ |- _ =>
        let x := fresh in
        pose proof H as x;
          apply H' in x
    end.

  Context {rri : raft_refinement_interface}.
  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.

  Lemma one_leader_per_term_invariant' :
    forall net,
      votes_correct net ->
      cronies_correct net ->
      one_leader_per_term (deghost net).
  Proof.
    unfold votes_correct, cronies_correct, one_leader_per_term in *.
    intuition.
    repeat match goal with
             | H : context [ nwState (deghost _) _ ] |- _ =>
               rewrite deghost_spec in H
           end.
    match goal with
      | h : type _ = _, h' : type _ = _ |- _ =>
        copy_eapply_prop_hyp votes_received_leaders h;
          copy_eapply_prop_hyp votes_received_leaders h'
    end.
    match goal with
      | H : wonElection _ = _ |- _ =>
        find_eapply_lem_hyp wonElection_one_in_common; [|clear H; eauto]
    end.
    break_exists; intuition.
    eapply_prop one_vote_per_term;
      eapply_prop cronies_votes;
      [eapply_prop votes_received_cronies|];
      intuition eauto.
    unfold raft_data in *. unfold raft_refined_base_params, raft_refined_multi_params in *.
    repeat find_rewrite.
    eapply_prop votes_received_cronies; intuition eauto.
  Qed.

  Theorem one_leader_per_term_invariant :
    forall net,
      raft_intermediate_reachable net -> one_leader_per_term net.
  Proof.
    intros.
    apply lower_prop; auto.
    intros.
    apply one_leader_per_term_invariant'.
    - eauto using votes_correct_invariant.
    - eauto using cronies_correct_invariant.
  Qed.

  Instance olpti : one_leader_per_term_interface.
  Proof.
    split.
    auto using one_leader_per_term_invariant.
  Qed.
End OneLeaderPerTermProof.
