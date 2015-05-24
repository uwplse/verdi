Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Omega.

Require Import Util.
Require Import Net.
Require Import Raft.
Require Import VerdiTactics.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RaftRefinementInterface.

Require Import PrevLogCandidateEntriesTermInterface.
Require Import VotesCorrectInterface.
Require Import CroniesCorrectInterface.
Require Import LeaderSublogInterface.

Require Import PrevLogLeaderSublogInterface.

Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.


Section PrevLogLeaderSublogProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.

  Context {lsi : leader_sublog_interface}.

  Context {plceti : prevLog_candidateEntriesTerm_interface}.

  Lemma prevLog_leader_sublog_init :
   raft_net_invariant_init prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_init, prevLog_leader_sublog.
    simpl. intuition.
  Qed.

  Lemma handleClientRequest_log_In :
    forall h st client id c out st' ps e,
      handleClientRequest h st client id c = (out, st', ps) ->
      In e (log st) -> In e (log st').
  Proof.
    intros.
    find_apply_lem_hyp handleClientRequest_log.
    intuition.
    - find_rewrite. auto.
    - break_exists. intuition. find_rewrite. intuition.
  Qed.

  Lemma prevLog_leader_sublog_client_request :
    raft_net_invariant_client_request prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_client_request, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - break_if; eauto.
      find_copy_apply_lem_hyp handleClientRequest_type. break_and.
      repeat find_rewrite.
      eapply_prop_hyp In In; eauto.
      break_exists_exists. intuition.
      eauto using handleClientRequest_log_In.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      exfalso. eapply handleClientRequest_no_append_entries; eauto.
      subst. simpl in *. find_rewrite. eauto 10.
  Qed.

  Lemma prevLog_leader_sublog_timeout :
    raft_net_invariant_timeout prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_timeout, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - break_if; eauto.
      find_copy_apply_lem_hyp handleTimeout_type.
      intuition; repeat find_rewrite; try discriminate.
      eapply_prop_hyp In In; eauto.
      break_exists_exists. intuition.
      erewrite handleTimeout_log_same by eauto.
      eauto.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      exfalso. subst. simpl in *.
      eapply handleTimeout_packets; eauto.
      find_rewrite. eauto 10.
  Qed.

  Lemma handleAppendEntries_type_log :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      type st' = Follower \/ (type st' = type st /\ log st' = log st /\ currentTerm st' = currentTerm st).
  Proof.
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto.
  Qed.

  Lemma prevLog_leader_sublog_append_entries :
    raft_net_invariant_append_entries prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_append_entries, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
      find_rewrite. break_if; eauto.
      find_copy_apply_lem_hyp handleAppendEntries_type_log.
      intuition.
      + congruence.
      + repeat find_rewrite.
        eapply_prop_hyp In In; eauto.
    - find_apply_lem_hyp handleAppendEntries_not_append_entries.
      simpl in *. subst. exfalso. eauto 10.
  Qed.

  Lemma prevLog_leader_sublog_append_entries_reply :
    raft_net_invariant_append_entries_reply prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_append_entries_reply, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
      find_rewrite. break_if; eauto.
      find_copy_apply_lem_hyp handleAppendEntriesReply_log.
      find_rewrite.
      find_copy_apply_lem_hyp handleAppendEntriesReply_type.
      intuition; repeat find_rewrite; try discriminate.
      eauto.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and.
      exfalso. subst. simpl in *.
      find_apply_lem_hyp handleAppendEntriesReply_packets.
      subst. simpl in *. intuition.
  Qed.

  Lemma prevLog_leader_sublog_request_vote :
    raft_net_invariant_request_vote prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_request_vote, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
      find_rewrite. break_if; eauto.
      find_copy_apply_lem_hyp handleRequestVote_log.
      find_copy_apply_lem_hyp handleRequestVote_type.
      intuition; repeat find_rewrite; try discriminate.
      eauto.
    - find_apply_lem_hyp handleRequestVote_no_append_entries.
      simpl in *. subst. exfalso. eauto 10.
  Qed.


  Definition candidateEntriesTerm_lowered (net : network) t p : Prop :=
    In p (nwPackets net) ->
    pBody p = RequestVoteReply t true ->
    currentTerm (nwState net (pDst p)) = t ->
    wonElection (dedup name_eq_dec (pSrc p :: votesReceived (nwState net (pDst p)))) = true ->
    type (nwState net (pDst p)) <> Candidate.

  Lemma deghost_packet_exists :
    forall net p,
      In p (nwPackets (deghost net)) ->
      exists (q : packet (params := raft_refined_multi_params (raft_params := raft_params))),
        In q (nwPackets net) /\ p = deghost_packet q.
  Proof.
    unfold deghost.
    simpl.
    intros.
    do_in_map.
    eauto.
  Qed.

  Lemma prevLog_candidateEntriesTerm_lowered' :
    forall net,
      prevLog_candidateEntriesTerm net ->
      votes_correct net ->
      cronies_correct net ->
      forall p p' t leaderId prevLogIndex prevLogTerm entries leaderCommit,
        In p (nwPackets (deghost net)) ->
        pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                                entries leaderCommit ->
        candidateEntriesTerm_lowered (deghost net) prevLogTerm p'.
  Proof.
    unfold candidateEntriesTerm_lowered,
           cronies_correct, votes_correct.
    intros. break_and.
    rewrite deghost_spec.

    find_apply_lem_hyp deghost_packet_exists.
    find_apply_lem_hyp deghost_packet_exists.
    break_exists.  break_and. subst.
    eapply_prop_hyp votes_nw pBody. concludes.
    eapply_prop_hyp prevLog_candidateEntriesTerm pBody; auto.

    unfold candidateEntriesTerm in *. break_exists. break_and.

    match goal with
    | H : wonElection _ = _ |- _ =>
      eapply wonElection_one_in_common in H; [|clear H; eauto]
    end.
    break_exists. break_and.
    repeat match goal with
           | [ H : _ |- _ ] => rewrite deghost_spec in H
           end.

    simpl in *.
    break_or_hyp.
    - apply_prop_hyp cronies_votes In.
      assert (pDst x = x1) by (eapply_prop one_vote_per_term; eauto).
      subst. auto.
    - intro.
      assert (pDst x = x1).
      { eapply_prop one_vote_per_term;
        eapply_prop cronies_votes.
        - eapply_prop votes_received_cronies; eauto.
        - repeat find_reverse_rewrite. auto.
      }
      subst.
      concludes. contradiction.
  Qed.

  Lemma prevLog_candidateEntriesTerm_lowered :
    forall net,
      raft_intermediate_reachable net ->
      forall p p' t leaderId prevLogIndex prevLogTerm entries leaderCommit,
        In p (nwPackets net) ->
        pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                                entries leaderCommit ->
        candidateEntriesTerm_lowered net prevLogTerm p'.
  Proof.
    intros net H.
    pattern net.
    apply lower_prop; auto.
    clear H net.
    intros.

    eapply prevLog_candidateEntriesTerm_lowered';
      eauto using prevLog_candidateEntriesTerm_invariant, votes_correct_invariant,
      cronies_correct_invariant.
  Qed.

  Lemma handleRequestVoteReply_type_term_won :
    forall h st src t v st',
      handleRequestVoteReply h st src t v = st' ->
      type st' = type st \/
      type st' = Follower \/
      (v = true /\
       wonElection (dedup name_eq_dec (src :: votesReceived st)) = true /\
       currentTerm st' = t).
  Proof.
    unfold handleRequestVoteReply.
    intros.
    repeat break_match; repeat find_inversion; subst; simpl in *; auto; do_bool; intuition.
  Qed.

  Lemma prevLog_leader_sublog_request_vote_reply :
    raft_net_invariant_request_vote_reply prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_request_vote_reply, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp.
    find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
    find_rewrite. break_if; eauto.
    find_copy_apply_lem_hyp handleRequestVoteReply_type.
    find_copy_apply_lem_hyp handleRequestVoteReply_log.
    intuition; repeat find_rewrite.
    - eauto.
    - discriminate.
    - exfalso.
      find_apply_lem_hyp handleRequestVoteReply_type_term_won.
      intuition; try congruence.
      eapply prevLog_candidateEntriesTerm_lowered with (p := p0) ; eauto.
      + congruence.
      + congruence.
  Qed.

  Lemma doLeader_messages :
    forall st h os st' ms m t n pli plt es ci,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      t = currentTerm st /\
      log st' = log st /\
      type st = Leader /\
      ((plt = 0) \/
       ((exists e, findAtIndex (log st) pli = Some e /\
              eTerm e = plt))).
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    break_match; try solve [find_inversion; simpl in *; intuition].
    break_if; try solve [find_inversion; simpl in *; intuition].
    find_inversion. simpl. do_in_map. subst.
    simpl in *. find_inversion. intuition.
    match goal with
      | |- context [pred ?x] =>
        remember (pred x) as index
    end. break_match; simpl in *.
    - right. eauto.
    - destruct index; intuition.
  Qed.

  Lemma prevLog_leader_sublog_do_leader :
    raft_net_invariant_do_leader prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_do_leader, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - break_if; eauto.
      find_copy_apply_lem_hyp doLeader_type. break_and.
      find_copy_apply_lem_hyp doLeader_log.
      repeat find_rewrite. eauto.
    - find_apply_lem_hyp in_map_iff. break_exists. break_and. subst.
      simpl in *.
      find_copy_eapply_lem_hyp doLeader_messages; eauto.
      intuition.
      + omega.
      + break_exists. break_and. subst.
        exists x0. find_apply_lem_hyp findAtIndex_elim. intuition.
        break_if.
        * congruence.
        * pose proof (leader_sublog_invariant_invariant _ $(eauto)$).
          unfold leader_sublog_invariant, leader_sublog_host_invariant in *. break_and.
          eauto.
  Qed.

  Lemma prevLog_leader_sublog_do_generic_server :
    raft_net_invariant_do_generic_server prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_do_generic_server, prevLog_leader_sublog.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp. break_or_hyp.
    - break_if; eauto.
      find_copy_eapply_lem_hyp doGenericServer_type. break_and.
      find_copy_eapply_lem_hyp doGenericServer_log.
      repeat find_rewrite.
      eauto.
    - find_copy_eapply_lem_hyp doGenericServer_packets.
      subst. simpl in *. intuition.
  Qed.

  Lemma prevLog_leader_sublog_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, prevLog_leader_sublog.
    intros.
    find_apply_hyp_hyp.
    repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Lemma prevLog_leader_sublog_reboot :
    raft_net_invariant_reboot prevLog_leader_sublog.
  Proof.
    unfold raft_net_invariant_reboot, prevLog_leader_sublog, reboot.
    intros.  subst. simpl in *.
    repeat find_reverse_higher_order_rewrite.

    match goal with
    | [ H : context [In _ _], H' : In _ _ |- _ ] =>
      eapply H with (leader0 := leader) in H'; eauto
    end.
    - break_exists_exists. intuition.
      repeat find_higher_order_rewrite.
      break_if; subst; simpl in *; auto.
    - repeat find_higher_order_rewrite.
      break_if; subst; simpl in *; auto.
      discriminate.
    - repeat find_higher_order_rewrite.
      break_if; subst; simpl in *; auto.
  Qed.

  Lemma prevLog_leader_sublog_invariant :
    forall net,
      raft_intermediate_reachable net ->
      prevLog_leader_sublog net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply prevLog_leader_sublog_init.
    - apply prevLog_leader_sublog_client_request.
    - apply prevLog_leader_sublog_timeout.
    - apply prevLog_leader_sublog_append_entries.
    - apply prevLog_leader_sublog_append_entries_reply.
    - apply prevLog_leader_sublog_request_vote.
    - apply prevLog_leader_sublog_request_vote_reply.
    - apply prevLog_leader_sublog_do_leader.
    - apply prevLog_leader_sublog_do_generic_server.
    - apply prevLog_leader_sublog_state_same_packet_subset.
    - apply prevLog_leader_sublog_reboot.
  Qed.

  Instance pllsi : prevLog_leader_sublog_interface.
  Proof.
    constructor.
    apply prevLog_leader_sublog_invariant.
  Qed.
End PrevLogLeaderSublogProof.
