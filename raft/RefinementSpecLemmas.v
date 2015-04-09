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
Require Import SpecLemmas.

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

  Lemma update_elections_data_client_request_allEntries :
    forall h st client id c out st' ms,
      handleClientRequest h (snd st) client id c = (out, st', ms) ->
      allEntries (update_elections_data_client_request h st client id c) =
      allEntries (fst st) \/
      (exists e : entry,
         eIndex e = S (maxIndex (log (snd st))) /\
         eTerm e = currentTerm (snd st) /\
         eClient e = client /\ eInput e = c /\ eId e = id /\ type (snd st) = Leader /\
         allEntries (update_elections_data_client_request h st client id c) =
         (currentTerm st', e) :: allEntries (fst st)).
  Proof.
    intros.
    unfold update_elections_data_client_request.
    repeat break_match; repeat find_inversion; auto.
    simpl.
    find_copy_apply_lem_hyp handleClientRequest_log.
    intuition.
    - repeat find_rewrite. do_bool. omega.
    - right.  break_exists_exists. intuition.
      congruence.
  Qed.
  
  Lemma update_elections_data_requestVoteReply_allEntries :
    forall h h' t  st r,
      allEntries (update_elections_data_requestVoteReply h h' t r st) = allEntries (fst st).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma handleAppendEntriesReply_entries :
    forall h st t h' pli plt es ci st' t' es',
      handleAppendEntries h st t h' pli plt es ci =
      (st', AppendEntriesReply t' es' true) ->
      es' = es.
  Proof.
    intros. unfold handleAppendEntries in *.
    repeat break_match; find_inversion; congruence.
  Qed.

  Lemma update_elections_data_appendEntries_allEntries :
    forall h st t h' pli plt es ci e,
      In e (map snd (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci))) ->
      In e (map snd (allEntries (fst st))) \/ In e es.
  Proof.
    intros.
    unfold update_elections_data_appendEntries in *.
    repeat break_match; subst; simpl in *; auto.
    find_apply_lem_hyp handleAppendEntriesReply_entries. subst.
    do_in_map. do_in_app. subst. intuition.
    - do_in_map. subst. simpl in *. auto.
    - left. apply in_map_iff. eexists; eauto.
  Qed.

  Lemma update_elections_data_clientRequest_allEntries_new :
    forall h st client id c e,
      In e (map snd (allEntries (update_elections_data_client_request h st client id c))) ->
      In e (map snd (allEntries (fst st))) \/
      (eIndex e = S (maxIndex (log (snd st)))
       /\ eTerm e = currentTerm (snd st)
       /\ type (snd st) = Leader).
  Proof.
    intros.
    unfold update_elections_data_client_request in *.
    repeat break_match; subst; simpl in *; auto. intuition. subst.
    do_bool. find_apply_lem_hyp handleClientRequest_log.
    intuition.
    - match goal with
        | H : log _ = log (snd _) |- _ => symmetry in H
      end. repeat find_rewrite. simpl in *. omega.
    - break_exists. intuition. repeat find_rewrite.
      find_inversion. intuition.
  Qed.

  Lemma update_elections_data_clientRequest_allEntries_old :
    forall h st client id c e,
      In e (map snd (allEntries (fst st))) ->
      In e (map snd (allEntries (update_elections_data_client_request h st client id c))).
  Proof.
    intros.
    unfold update_elections_data_client_request in *.
    repeat break_match; subst; simpl in *; auto. 
  Qed.

  Lemma update_elections_data_timeout_allEntries :
    forall h st,
      allEntries (update_elections_data_timeout h st) = allEntries (fst st).
  Proof.
    intros.
    unfold update_elections_data_timeout. repeat break_match; simpl; auto.
  Qed.

  Lemma update_elections_data_requestVote_allEntries :
    forall h h' t lli llt st,
      allEntries (update_elections_data_requestVote h h' t h' lli llt st) =
      allEntries (fst st).
  Proof.
    unfold update_elections_data_requestVote.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma update_elections_data_client_request_cronies :
    forall h st client id c out st' ms,
      handleClientRequest h (snd st) client id c = (out, st', ms) ->
      cronies (update_elections_data_client_request h st client id c) =
      cronies (fst st).
  Proof.
    intros.
    unfold update_elections_data_client_request.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma update_elections_data_appendEntries_cronies :
    forall h st t h' pli plt es ci,
      cronies (update_elections_data_appendEntries h st t h' pli plt es ci) =
      cronies (fst st).
  Proof.
    intros.
    unfold update_elections_data_appendEntries in *.
    repeat break_match; subst; simpl in *; auto.
  Qed.

  Lemma update_elections_data_clientRequest_cronies_new :
    forall h st client id c,
      cronies (update_elections_data_client_request h st client id c) =
      cronies (fst st).
  Proof.
    intros.
    unfold update_elections_data_client_request in *.
    repeat break_match; subst; simpl in *; auto.
  Qed.
  
  Lemma update_elections_data_timeout_cronies :
    forall h st t,
      cronies (update_elections_data_timeout h st) t = cronies (fst st) t
      \/ (cronies (update_elections_data_timeout h st) t = [h]
          /\ t = S (currentTerm (snd st))).
  Proof.
    intros.
    unfold update_elections_data_timeout. repeat break_match; simpl; auto.
    unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; simpl in *; auto; congruence.
  Qed.

  Lemma update_elections_data_requestVote_cronies :
    forall h h' t lli llt st,
      cronies (update_elections_data_requestVote h h' t h' lli llt st) =
      cronies (fst st).
  Proof.
    unfold update_elections_data_requestVote.
    intros.
    repeat break_match; auto.
  Qed.
  
End SpecLemmas.
