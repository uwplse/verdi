Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import Omega.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import RefinementCommonTheorems.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LeaderLogsVotesWithLogInterface.
Require Import VotesCorrectInterface.
Require Import CroniesCorrectInterface.
Require Import VotesVotesWithLogCorrespondInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import OneLeaderLogPerTermInterface.

Section OneLeaderLogPerTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rri : raft_refinement_interface}.

  Context {llvwli : leaderLogs_votesWithLog_interface}.
  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.
  Context {vvci : votes_votesWithLog_correspond_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac start :=
    red; unfold one_leaderLog_per_term; simpl; intros.

  Ltac start_update :=
    start;
    repeat find_higher_order_rewrite;
    repeat (update_destruct; subst; rewrite_update);
    [| | |eauto].

  Lemma one_leaderLog_per_term_init :
    refined_raft_net_invariant_init one_leaderLog_per_term.
  Proof.
    start. contradiction.
  Qed.

  Lemma one_leaderLog_per_term_unchanged :
    forall net st' ps' h gd d,
      one_leaderLog_per_term net ->
      (forall h' : Net.name, st' h' = update (nwState net) h (gd, d) h') ->
      leaderLogs gd = leaderLogs (fst (nwState net h)) ->
      one_leaderLog_per_term {| nwPackets := ps'; nwState := st' |}.
  Proof.
    unfold one_leaderLog_per_term. intros.
    repeat find_higher_order_rewrite;
    repeat (update_destruct; subst; rewrite_update);
    simpl in *; repeat find_rewrite; eauto.
  Qed.

  Ltac start_unchanged :=
    red; intros; eapply one_leaderLog_per_term_unchanged; eauto; subst.

  (* solve invariant by lemma which shows leader logs do not change *)
  Ltac unchanged lem :=
    start_unchanged; apply lem.

  Lemma one_leaderLog_per_term_client_request :
    refined_raft_net_invariant_client_request one_leaderLog_per_term.
  Proof.
    unchanged update_elections_data_client_request_leaderLogs.
  Qed.

  Lemma one_leaderLog_per_term_timeout :
    refined_raft_net_invariant_timeout one_leaderLog_per_term.
  Proof.
    unchanged update_elections_data_timeout_leaderLogs.
  Qed.

  Lemma one_leaderLog_per_term_append_entries :
    refined_raft_net_invariant_append_entries one_leaderLog_per_term.
  Proof.
    unchanged update_elections_data_appendEntries_leaderLogs.
  Qed.

  Lemma one_leaderLog_per_term_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply one_leaderLog_per_term.
  Proof.
    start_unchanged. auto.
  Qed.

  Lemma one_leaderLog_per_term_request_vote :
    refined_raft_net_invariant_request_vote one_leaderLog_per_term.
  Proof.
    unchanged leaderLogs_update_elections_data_requestVote.
  Qed.

  Lemma update_elections_data_requestVoteReply_leaderLogs' :
    forall h h' t st t' ll' r,
      In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)) ->
      In (t', ll') (leaderLogs (fst st))
      \/ (r = true
          /\ t = currentTerm (snd st)
          /\ ll' = log (snd st)
          /\ t' = currentTerm (snd st)
          /\ type (snd st) = Candidate
          /\ wonElection (dedup name_eq_dec (h' :: votesReceived (snd st))) = true).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; auto.
    simpl in *. intuition.
    find_inversion. right.
    unfold handleRequestVoteReply in *.
    repeat break_match; simpl in *; intuition; try congruence;
    break_if; try congruence; do_bool; eauto using le_antisym.
  Qed.

  Lemma wonElection_length :
    forall votes,
      wonElection votes = true ->
      length votes > div2 (length nodes).
  Proof.
    unfold wonElection. intros. find_apply_lem_hyp leb_true_le. omega.
  Qed.

  Lemma pigeon_nodes :
    forall (q1 q2 : list name),
      NoDup q1 ->
      NoDup q2 ->
      length q1 > div2 (length nodes) ->
      length q2 > div2 (length nodes) ->
      exists v, In v q1 /\ In v q2.
  Proof.
    intros. eapply pigeon with (l := nodes).
    - apply name_eq_dec.
    - intros. apply (@all_names_nodes _ multi_params).
    - intros. apply (@all_names_nodes _ multi_params).
    - apply (@no_dup_nodes _ multi_params).
    - assumption.
    - assumption.
    - apply div2_correct; assumption.
  Qed.

  (* two different hosts cannot both have the same term in their leader logs *)
  Lemma contradiction_case :
    forall (net : network ) t ll ll' (h h' : name) (p : packet (params := refined_multi_params (multi_params := multi_params))) t0 v xs ys,
      refined_raft_intermediate_reachable net ->
      pBody p = RequestVoteReply (raft_params := raft_params) t0 v ->
      nwPackets net = xs ++ p :: ys ->
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In (t, ll') (leaderLogs (update_elections_data_requestVoteReply (pDst p) (pSrc p) t0 v (nwState net (pDst p)))) ->
      pDst p = h' ->
      pDst p <> h ->
      False.
  Proof.
    intros. unfold not in *. find_false.
    simpl in *. find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs'.
    intro_refined_invariant leaderLogs_votesWithLog_invariant.
    break_or_hyp; repeat (apply_prop_hyp leaderLogs_votesWithLog In; break_exists).
    - assert (exists h, In h x /\ In h x0) by (apply pigeon_nodes; intuition).
      break_exists; break_and.
      do 2 (find_apply_hyp_hyp; break_exists; break_and).
      intro_refined_invariant votes_votesWithLog_correspond_invariant.
      do 2 (apply_prop_hyp votes_votesWithLog In).
      intro_refined_invariant votes_correct_invariant.
      eauto.
    - assert (exists h, In h x /\ In h (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p)))))).
      { eapply pigeon_nodes.
        - intuition.
        - apply NoDup_dedup.
        - intuition.
        - apply wonElection_length; intuition. }
      break_exists. break_and.
      find_apply_hyp_hyp; break_exists; break_and.
      intro_refined_invariant votes_votesWithLog_correspond_invariant.
      apply_prop_hyp votes_votesWithLog In.
      find_apply_lem_hyp in_dedup_was_in.
      simpl in *.
      intro_refined_invariant cronies_correct_invariant.
      intro_refined_invariant votes_correct_invariant.
      break_or_hyp; eauto.
  Qed.

  Lemma one_leaderLog_per_term_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply one_leaderLog_per_term.
  Proof.
    start. repeat find_higher_order_rewrite. repeat (update_destruct; rewrite_update).
    - split; [subst; auto|].
      find_copy_eapply_lem_hyp leaderLogs_update_elections_data_RVR; [|eauto].
      pose proof H.
      eapply leaderLogs_update_elections_data_RVR with (ll0 := ll) in H; [|eauto].
      intro_refined_invariant leaderLogs_currentTerm_sanity_candidate_invariant.
      intuition.
      + match goal with
        | [ h: _ |- _ ] => solve[eapply h; eauto]
        end.
      + apply_prop_hyp leaderLogs_currentTerm_sanity_candidate nwState; auto.
        find_copy_apply_lem_hyp handleRequestVoteReply_type. intuition; unfold raft_data in *; simpl in *.
        * subst. repeat find_rewrite. discriminate.
        * find_apply_lem_hyp lt_asym. congruence.
        * subst. repeat find_rewrite. find_apply_lem_hyp lt_irrefl. contradiction.
      + apply_prop_hyp leaderLogs_currentTerm_sanity_candidate nwState; auto.
        find_copy_apply_lem_hyp handleRequestVoteReply_type. intuition; unfold raft_data in *; simpl in *.
        * subst. repeat find_rewrite. discriminate.
        * find_apply_lem_hyp lt_asym. congruence.
        * subst. repeat find_rewrite. find_apply_lem_hyp lt_irrefl. contradiction.
      + subst. auto.
    - exfalso. eapply contradiction_case; eauto.
    - exfalso. eapply contradiction_case; eauto.
    - eauto.
  Qed.

  Lemma one_leaderLog_per_term_do_leader :
    refined_raft_net_invariant_do_leader one_leaderLog_per_term.
  Proof.
    start_unchanged. find_rewrite. auto.
  Qed.

  Lemma one_leaderLog_per_term_do_generic_server :
    refined_raft_net_invariant_do_generic_server one_leaderLog_per_term.
  Proof.
    start_unchanged. find_rewrite. auto.
  Qed.

  Lemma one_leaderLog_per_term_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset one_leaderLog_per_term.
  Proof.
    start. repeat find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma one_leaderLog_per_term_reboot :
    refined_raft_net_invariant_reboot one_leaderLog_per_term.
  Proof.
    start_update; eapply H0; unfold reboot in *; try find_rewrite; simpl in *; eauto.
  Qed.

  Lemma one_leaderLog_per_term_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      one_leaderLog_per_term net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply one_leaderLog_per_term_init.
    - apply one_leaderLog_per_term_client_request.
    - apply one_leaderLog_per_term_timeout.
    - apply one_leaderLog_per_term_append_entries.
    - apply one_leaderLog_per_term_append_entries_reply.
    - apply one_leaderLog_per_term_request_vote.
    - apply one_leaderLog_per_term_request_vote_reply.
    - apply one_leaderLog_per_term_do_leader.
    - apply one_leaderLog_per_term_do_generic_server.
    - apply one_leaderLog_per_term_state_same_packet_subset.
    - apply one_leaderLog_per_term_reboot.
  Qed.

  Instance ollpti : one_leaderLog_per_term_interface.
  Proof.
    split; intros; intro_invariant one_leaderLog_per_term_invariant;
      red; eapply_prop one_leaderLog_per_term.
  Qed.

End OneLeaderLogPerTerm.
