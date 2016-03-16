Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import VotesReceivedMoreUpToDateInterface.
Require Import RequestVoteReplyMoreUpToDateInterface.

Require Import LeaderLogsVotesWithLogInterface.

Section LeaderLogsVotesWithLog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {vrmutdi : votesReceived_moreUpToDate_interface}.
  Context {rvrmutdi : requestVoteReply_moreUpToDate_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).


  Lemma quorum_preserved:
    forall (st st' : name -> electionsData * raft_data)
      (t0 : term) (ll : list entry) (leader : name),
      (forall h t leader log,
         In (t, leader, log) (votesWithLog (fst (st h))) ->
         In (t, leader, log) (votesWithLog (fst (st' h)))) ->
      (exists quorum : list name,
         NoDup quorum /\
         length quorum > div2 (length nodes) /\
         (forall h : name,
            In h quorum ->
            exists log : list entry,
              moreUpToDate (maxTerm ll) (maxIndex ll) (maxTerm log) (maxIndex log) =
              true /\ In (t0, leader, log) (votesWithLog (fst (st h))))) ->
      exists quorum : list name,
        NoDup quorum /\
        length quorum > div2 (length nodes) /\
        (forall h : name,
           In h quorum ->
           exists log : list entry,
             moreUpToDate (maxTerm ll) (maxIndex ll) (maxTerm log) (maxIndex log) =
             true /\ In (t0, leader, log) (votesWithLog (fst (st' h)))).
  Proof.
    intros.
    break_exists_exists. intuition.
    find_apply_hyp_hyp. break_exists_exists. intuition eauto.
  Qed.
  
  Lemma leaderLogs_votesWithLog_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
      eapply quorum_preserved; [|eauto].
      intros.
      find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      rewrite votesWithLog_same_append_entries. auto.
    - eapply quorum_preserved; [|eauto].
      intros.
      find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      rewrite votesWithLog_same_append_entries. auto.
  Qed.

  Lemma leaderLogs_votesWithLog_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - eapply quorum_preserved; [|eauto].
      intros.
      find_higher_order_rewrite; destruct_update; simpl in *; eauto.
    - eapply quorum_preserved; [|eauto].
      intros.
      find_higher_order_rewrite; destruct_update; simpl in *; eauto.
  Qed.

  Lemma update_elections_data_request_vote_votesWithLog_old :
    forall (h : name)
      (st : electionsData *
            RaftState.raft_data term name entry logIndex serverType data output)
      (t : nat) (src : fin N) (lli llt : nat)
      (t' : term) (h' : name) (l' : list entry),
      In (t', h', l') (votesWithLog (fst st)) ->
      In (t', h', l')
         (votesWithLog (update_elections_data_requestVote h src t src lli llt st)).
  Proof.
    intros.
    unfold update_elections_data_requestVote in *.
    repeat break_match; simpl in *; intuition.
  Qed.

  Lemma leaderLogs_votesWithLog_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    - find_rewrite_lem leaderLogs_update_elections_data_requestVote.
      eapply quorum_preserved; [|eauto].
      intros.
      find_higher_order_rewrite; destruct_update; simpl in *;
      eauto using update_elections_data_request_vote_votesWithLog_old.
    - eapply quorum_preserved; [|eauto].
      intros.
      find_higher_order_rewrite; destruct_update; simpl in *;
      eauto using update_elections_data_request_vote_votesWithLog_old.
  Qed.


  Require Import Omega.
  
  Lemma wonElection_dedup_spec :
    forall l,
      wonElection (dedup name_eq_dec l) = true ->
      exists quorum,
        NoDup quorum /\
        length quorum > div2 (length nodes) /\
        (forall h, In h quorum -> In h l).
  Proof.
    intros.
    exists (dedup name_eq_dec l). intuition; eauto using NoDup_dedup, in_dedup_was_in.
    unfold wonElection in *.
    do_bool. omega.
  Qed.
        
  Lemma leaderLogs_votesWithLog_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|eapply quorum_preserved; [|eauto];
      intros;
      find_higher_order_rewrite; destruct_update; simpl in *; eauto;
      rewrite update_elections_data_request_vote_reply_votesWithLog;
      auto].
    find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
    intuition;
      [eapply quorum_preserved; [|eauto];
       intros;
       find_higher_order_rewrite; destruct_update; simpl in *; eauto;
       rewrite update_elections_data_request_vote_reply_votesWithLog;
       auto|].
    subst.
    match goal with
      | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] =>
        remember (handleRequestVoteReply h st h' t r) as new_state
    end.
    find_eapply_lem_hyp handleRequestVoteReply_spec'.
    intuition.
    conclude_using 
      ltac:(repeat find_rewrite; congruence).
    concludes.
    intuition.
    repeat find_rewrite.
    find_apply_lem_hyp wonElection_dedup_spec.
    break_exists_exists. intuition.
    find_apply_hyp_hyp.
    simpl in *. intuition.
    - subst.
      find_eapply_lem_hyp requestVoteReply_moreUpToDate_invariant; eauto.
      repeat find_rewrite.
      repeat concludes.
      break_exists_exists. intuition.
      find_higher_order_rewrite.
      simpl in *.
      destruct_update; subst; simpl in *; eauto.
      repeat find_rewrite.
      rewrite update_elections_data_request_vote_reply_votesWithLog. auto.
    - find_eapply_lem_hyp votesReceived_moreUpToDate_invariant; eauto.
      break_exists_exists. intuition.
      find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      rewrite update_elections_data_request_vote_reply_votesWithLog. auto.
  Qed.

  Lemma update_elections_data_timeout_votesWithLog_old :
    forall h st t h' l,
      In (t, h', l) (votesWithLog (fst st)) ->
      In (t, h', l) (votesWithLog (update_elections_data_timeout h st)).
  Proof.
    intros.
    unfold update_elections_data_timeout.
    repeat break_match; simpl in *; auto.
  Qed.

  Lemma leaderLogs_votesWithLog_timeout :
    refined_raft_net_invariant_timeout leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|eapply quorum_preserved; [|eauto];
      intros;
      find_higher_order_rewrite; destruct_update; simpl in *; eauto;
      apply update_elections_data_timeout_votesWithLog_old;
      auto].
    find_rewrite_lem update_elections_data_timeout_leaderLogs.
    eapply quorum_preserved; [|eauto];
      intros;
      find_higher_order_rewrite; destruct_update; simpl in *; eauto;
      apply update_elections_data_timeout_votesWithLog_old;
      auto.
  Qed.

  Lemma leaderLogs_votesWithLog_client_request :
    refined_raft_net_invariant_client_request leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    [|eapply quorum_preserved; [|eauto];
      intros;
      find_higher_order_rewrite; destruct_update; simpl in *; eauto;
      rewrite votesWithLog_same_client_request;
      auto].
    find_rewrite_lem update_elections_data_client_request_leaderLogs.
    eapply quorum_preserved; [|eauto];
      intros;
      find_higher_order_rewrite; destruct_update; simpl in *; eauto;
      rewrite votesWithLog_same_client_request;
      auto.
  Qed.

  Lemma leaderLogs_votesWithLog_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    solve [eapply quorum_preserved; [|eauto];
           intros;
           find_higher_order_rewrite; destruct_update; simpl in *; eauto;
           auto].
  Qed.

  Lemma leaderLogs_votesWithLog_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    solve [eapply quorum_preserved; [|eauto];
           intros;
           find_higher_order_rewrite; destruct_update; simpl in *; eauto;
           auto].
  Qed.

  Lemma leaderLogs_votesWithLog_reboot :
    refined_raft_net_invariant_reboot leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto;
    solve [eapply quorum_preserved; [|eauto];
           intros;
           find_higher_order_rewrite; destruct_update; simpl in *; eauto;
           auto].
  Qed.

  Lemma leaderLogs_votesWithLog_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    subst. repeat find_reverse_higher_order_rewrite.
    eapply quorum_preserved; [|eauto];
    intros;
    find_higher_order_rewrite; destruct_update; simpl in *; eauto;
    auto.
  Qed.

  Lemma leaderLogs_votesWithLog_init :
    refined_raft_net_invariant_init leaderLogs_votesWithLog.
  Proof.
    red. unfold leaderLogs_votesWithLog. intros. simpl in *.
    intuition.
  Qed.
  
  Instance llvwli : leaderLogs_votesWithLog_interface.
  split.
  intros.
  apply refined_raft_net_invariant; auto.
  - apply leaderLogs_votesWithLog_init.
  - apply leaderLogs_votesWithLog_client_request.
  - apply leaderLogs_votesWithLog_timeout.
  - apply leaderLogs_votesWithLog_append_entries.
  - apply leaderLogs_votesWithLog_append_entries_reply.
  - apply leaderLogs_votesWithLog_request_vote.
  - apply leaderLogs_votesWithLog_request_vote_reply.
  - apply leaderLogs_votesWithLog_do_leader.
  - apply leaderLogs_votesWithLog_do_generic_server.
  - apply leaderLogs_votesWithLog_state_same_packet_subset.
  - apply leaderLogs_votesWithLog_reboot.
  Qed.
  
End LeaderLogsVotesWithLog.
