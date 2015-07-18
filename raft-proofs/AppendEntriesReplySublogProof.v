Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.

Require Import CommonTheorems.
Require Import RefinementCommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AppendEntriesReplySublogInterface.

Require Import AppendEntriesRequestReplyCorrespondenceInterface.
Require Import RaftRefinementInterface.
Require Import AllEntriesLeaderLogsInterface.

Section AppendEntriesReplySublog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {aerrci : append_entries_request_reply_correspondence_interface}.
  Context {rri : raft_refinement_interface}.
  Context {aelli : all_entries_leader_logs_interface}.

  Definition lowered_appendEntries_leader (net : @network _ multi_params)  :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit h e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      In e entries ->
      currentTerm (nwState net h) = t ->
      type (nwState net h) = Leader ->
      In e (log (nwState net h)).

  Theorem lower_appendEntries_leader :
    forall net,
      raft_intermediate_reachable net ->
      lowered_appendEntries_leader net.
  Proof.
    intros.
    apply (lower_prop lowered_appendEntries_leader); auto.
    intros.
    find_apply_lem_hyp all_entries_leader_logs_invariant.
    unfold all_entries_leader_logs in *. intuition.
    unfold lowered_appendEntries_leader, appendEntries_leader in *.
    intros. simpl in *.
    repeat break_match. simpl in *.
    do_in_map. subst. simpl in *.
    match goal with
      | H : ?nwState  ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    eapply_prop_hyp AppendEntries AppendEntries; eauto.
  Qed.

  Theorem append_entries_reply_sublog_invariant :
    forall net,
      raft_intermediate_reachable net ->
      append_entries_reply_sublog net.
  Proof.
    unfold append_entries_reply_sublog. intros.
    find_apply_lem_hyp append_entries_request_reply_correspondence_invariant.
    eapply_prop_hyp append_entries_request_reply_correspondence AppendEntriesReply; eauto.
    unfold exists_equivalent_network_with_aer in *.
    break_exists_name net'. break_exists. intuition.
    match goal with
      | _ : nwPackets _ = _ ++ (mkPacket ?s ?d ?b) :: nil |- _ =>
        remember (mkPacket s d b) as aer;
          assert (pBody aer = b) by (subst; simpl; auto);
          clear Heqaer
    end.
    match goal with
      | H : In _ (nwPackets _) |- _ => clear H
    end.
    assert (In aer (nwPackets net')) by (repeat find_rewrite; intuition).
    match goal with
      | H : nwState net' = nwState net |- _ =>
        rewrite <- H in *; clear H
    end.
    eapply lower_appendEntries_leader; eauto.
  Qed.
  
  Instance aersi : append_entries_reply_sublog_interface.
  split. exact append_entries_reply_sublog_invariant.
  Qed.
End AppendEntriesReplySublog.
