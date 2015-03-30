Require Import List.
Import ListNotations.

Require Import PeanoNat.
Require Import Arith.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import VotesCorrectInterface.
Require Import CroniesCorrectInterface.

Require Import CommonTheorems.
Require Import RefinementCommonDefinitions.

Section CommonTheorems.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma candidateEntries_wonElection :
    forall (net : network (params := raft_refined_multi_params))  e h,
      one_vote_per_term net ->
      cronies_votes net ->
      votes_received_cronies net ->
      candidateEntries e (nwState net) ->
      currentTerm (snd (nwState net h)) = eTerm e ->
      wonElection (dedup name_eq_dec (votesReceived (snd (nwState net h)))) = true ->
      type (snd (nwState net h)) <> Candidate.
  Proof.
    intros.
    unfold candidateEntries in *. break_exists. break_and.
    repeat match goal with
             | [ H : _ |- _ ] => rewrite deghost_spec in H
           end.
    intro.
    assert (x = h).
    {
      match goal with
        | H : wonElection _ = _ |- _ =>
          eapply wonElection_one_in_common in H; [|clear H; eauto]
      end.
      break_exists. break_and.

      eapply_prop one_vote_per_term;
        try solve [eapply_prop cronies_votes; eauto].
      eapply_prop cronies_votes.
      repeat find_reverse_rewrite.
      eapply_prop votes_received_cronies; auto.
    }
    subst.
    concludes.
    contradiction.
  Qed.

  Lemma wonElection_candidateEntries_rvr :
    forall (net : network (params := raft_refined_multi_params)) p e,
      votes_correct net ->
      cronies_correct net ->
      candidateEntries e (nwState net) ->
      In p (nwPackets net) ->
      pBody p = RequestVoteReply (eTerm e) true ->
      currentTerm (snd (nwState net (pDst p))) = eTerm e ->
      wonElection (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p))))) = true ->
      type (snd (nwState net (pDst p))) <> Candidate.
  Proof.
    unfold votes_correct, cronies_correct.
    intros. break_and.

    match goal with
      | [ H : context [ votes_nw ], H' : context [ pBody ] |- _ ] =>
        eapply H in H'
    end.

    unfold candidateEntries in *. break_exists. break_and.
    match goal with
      | H : wonElection _ = _ |- _ =>
        eapply wonElection_one_in_common in H; [|clear H; eauto]
    end.
    break_exists.
    break_and.
    simpl in *.
    intuition.
    - subst.
      apply_prop_hyp cronies_votes In.
      assert (x = pDst p) by (eapply_prop one_vote_per_term; eauto).
      subst. concludes. contradiction.
    - apply_prop_hyp votes_received_cronies In. concludes.
      apply_prop_hyp cronies_votes In.
      apply_prop_hyp cronies_votes In.
      unfold raft_data in *. unfold raft_refined_base_params, raft_refined_multi_params in *.
      simpl in *.
      repeat find_reverse_rewrite.
      assert (x = pDst p) by (eapply_prop one_vote_per_term; eauto).
      subst.
      repeat concludes. contradiction.
  Qed.
End CommonTheorems.