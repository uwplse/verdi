Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import CommonTheorems.
Require Import RefinementCommonTheorems.

Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import OneLeaderLogPerTermInterface.
Require Import LeaderLogsSortedInterface.
Require Import RefinedLogMatchingLemmasInterface.
Require Import AppendEntriesRequestsCameFromLeadersInterface.
Require Import AllEntriesLogInterface.
Require Import LeaderSublogInterface.
Require Import LeadersHaveLeaderLogsStrongInterface.

Require Import AllEntriesLeaderLogsInterface.

Section AllEntriesLeaderLogs.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {aerlli : append_entries_leaderLogs_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {llsi : leaderLogs_sorted_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {aercfli : append_entries_came_from_leaders_interface}.
  Context {aeli : allEntries_log_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {lhsi : leaders_have_leaderLogs_strong_interface}.

  Lemma leader_without_missing_entry_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_without_missing_entry net.
  Proof.
    intros. unfold leader_without_missing_entry.
    find_apply_lem_hyp allEntries_log_invariant.
    unfold allEntries_log in *.
    intros. copy_eapply_prop_hyp allEntries allEntries.
    intuition. right. break_exists; intuition; repeat eexists; eauto.
  Qed.

  Lemma appendEntriesRequest_exists_leaderLog_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntriesRequest_exists_leaderLog net.
  Proof.
    intros. unfold appendEntriesRequest_exists_leaderLog.
    apply append_entries_came_from_leaders_invariant; auto.
  Qed.

  Lemma appendEntriesRequest_leaderLog_not_in_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntriesRequest_leaderLog_not_in net.
  Proof.
    unfold appendEntriesRequest_leaderLog_not_in.
    intros.
    find_copy_apply_lem_hyp append_entries_leaderLogs_invariant.
    unfold append_entries_leaderLogs in *.
    pose proof entries_sorted_nw_invariant net $(auto)$ p _ _ _ _ _ _ $(auto)$ $(eauto)$.
    match goal with
    | [ H : In _ (nwPackets _), H' : forall _, _ |- _ ] =>
      copy_eapply H' H
    end; eauto.
    break_exists. break_and.
    pose proof one_leaderLog_per_term_invariant _ $(eauto)$ (pSrc p) x _ _  _ $(eauto)$ $(eauto)$.
    break_and. subst.
    intro.
    match goal with
    | [ H : ~ In _ _ |- _ ] => apply H
    end.
    apply in_or_app. right.
    find_copy_apply_lem_hyp leaderLogs_sorted_invariant; auto.
    find_copy_eapply_lem_hyp maxIndex_is_max; eauto.
    intuition.
    - break_and. subst. omega.
    - break_exists. intuition. subst.
      unfold Prefix_sane in *. intuition.
      + eapply prefix_contiguous; eauto.
        pose proof entries_contiguous_nw_invariant _ $(eauto)$ p _ _ _ _ _ _ $(auto)$ $(eauto)$.
        eapply contiguous_app ; eauto.
      + omega.
    - subst. auto.
  Qed.

  Lemma lift_leader_sublog_nw :
    forall net (leader : Net.name) (p : packet) (t : term) 
      (leaderId : name) (prevLogIndex : logIndex) (prevLogTerm : term)
      (entries : list entry) (leaderCommit : logIndex) 
      (e : entry),
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net leader)) = Leader ->
      In p (nwPackets net) ->
      pBody p =
      AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      In e entries ->
      eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
  Proof.
    intros.
    pose proof lift_prop _ leader_sublog_invariant_invariant $(eauto)$ $(eauto)$.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant in *. intuition.
    find_apply_lem_hyp ghost_packet.
    simpl in *. repeat break_match.
    simpl.
    match goal with
      | H : context [pBody] |- _ =>
        solve [eapply H; simpl in *; eauto]
    end.
  Qed.
  
  Lemma appendEntries_leader_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      appendEntries_leader net.
  Proof.
    unfold appendEntries_leader. intros.
    subst.
    find_copy_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
    break_exists; intuition. repeat find_rewrite.
    find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
    break_exists; repeat break_and.
    match goal with
      | H : context [Prefix_sane] |- _ =>
        clear H
    end.
    find_eapply_lem_hyp one_leaderLog_per_term_invariant; eauto.
    conclude_using eauto. intuition; subst.
    do_in_app; intuition;
    [|eapply in_app_iff;
       eauto using Prefix_in].
    find_copy_apply_hyp_hyp.
    find_eapply_lem_hyp lift_leader_sublog_nw; eauto; repeat find_rewrite; eauto.
    eapply in_app_iff. auto.
  Qed.

  Lemma leaderLogs_leader_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_leader net.
  Proof.
    unfold leaderLogs_leader. intros.
    find_apply_lem_hyp leaders_have_leaderLogs_strong_invariant; auto.
    break_exists_exists. intuition.
  Qed.

  Instance aelli :  all_entries_leader_logs_interface.
  Proof.
    split.
    intros.
    red.
    intuition.
    - auto using leader_without_missing_entry_invariant.
    - auto using appendEntriesRequest_exists_leaderLog_invariant.
    - auto using appendEntriesRequest_leaderLog_not_in_invariant.
    - auto using appendEntries_leader_invariant.
    - auto using leaderLogs_leader_invariant.
  Qed.
End AllEntriesLeaderLogs.
