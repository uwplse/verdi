Require Import List.
Import ListNotations.
Require Import Min.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonTheorems.
Require Import RaftRefinementInterface.

Section SpecLemmas.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Lemma update_elections_data_client_request_leaderLogs :
    forall h st client id c,
      leaderLogs (update_elections_data_client_request h st client id c) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_client_request in *.
    intros. repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma update_elections_data_timeout_leaderLogs :
    forall h st,
      leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma update_elections_data_appendEntries_leaderLogs :
    forall h st t src pli plt es ci,
      leaderLogs (update_elections_data_appendEntries h st t src pli plt es ci) = leaderLogs (fst st).
  Proof.
    unfold update_elections_data_appendEntries.
    intros. repeat break_match; auto.
  Qed.

  Lemma leaderLogs_update_elections_data_requestVote :
    forall h src t ci lli llt st,
      leaderLogs (update_elections_data_requestVote h src t ci lli llt st) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_requestVote.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma leaderLogs_update_elections_data_RVR :
    forall h src t1 v st t2 ll st',
      handleRequestVoteReply h (snd st) src t1 v = st' ->
      In (t2, ll) (leaderLogs (update_elections_data_requestVoteReply h src t1 v st)) ->
      In (t2, ll) (leaderLogs (fst st)) \/
      (type st' = Leader /\
       type (snd st) = Candidate /\
       t2 = currentTerm st' /\
       ll = log st').
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; repeat find_inversion; intuition.
    simpl in *. intuition.
    find_inversion. intuition.
  Qed.
End SpecLemmas.