Require Import Raft.
Require Import RaftRefinementInterface.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import LeadersHaveLeaderLogsInterface.
Require Import AppendEntriesRequestsCameFromLeadersInterface.

Section AppendEntriesRequestsCameFromLeaders.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhlli : leaders_have_leaderLogs_interface}.
  Context {rri : raft_refinement_interface}.

  Ltac start :=
    red; unfold append_entries_came_from_leaders; intros;
    subst; simpl in *; find_higher_order_rewrite;
    update_destruct_hyp; subst; rewrite_update; eauto; simpl in *.

  Ltac prove_in :=
    match goal with
      | [ _ : nwPackets ?net = _,
              _ : In (?p : packet) _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition)
      | [ _ : nwPackets ?net = _,
              _ : pBody ?p = _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; intuition)
    end.

  Ltac contra :=  (exfalso; intuition; find_false;
                   repeat eexists; eauto).

  Lemma append_entries_came_from_leaders_appendEntries :
    refined_raft_net_invariant_append_entries append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
      rewrite update_elections_data_appendEntries_leaderLogs. repeat find_rewrite.
      eauto.
    - subst. simpl in *. subst.
      find_apply_lem_hyp handleAppendEntries_not_append_entries.
      exfalso. intuition. find_false.
      repeat eexists; eauto.
  Qed.

  Lemma append_entries_came_from_leaders_appendEntriesReply :
    refined_raft_net_invariant_append_entries_reply append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
      repeat find_rewrite. eauto. 
    - subst. simpl in *. subst.
      find_apply_lem_hyp handleAppendEntriesReply_packets.
      subst. simpl in *. intuition.
  Qed.


  Lemma append_entries_came_from_leaders_requestVote :
    refined_raft_net_invariant_request_vote append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
      rewrite leaderLogs_update_elections_data_requestVote. repeat find_rewrite.
      eauto.
    - subst. simpl in *. subst.
      find_apply_lem_hyp handleRequestVote_no_append_entries.
      contra.
  Qed.


  Lemma append_entries_came_from_leaders_requestVoteReply :
    refined_raft_net_invariant_request_vote_reply append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    prove_in. find_apply_hyp_hyp.
    break_exists.
    repeat find_higher_order_rewrite.
    update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
    eexists.
    eapply update_elections_data_requestVoteReply_old. repeat find_rewrite. eauto.
  Qed.


  Lemma append_entries_came_from_leaders_clientRequest :
    refined_raft_net_invariant_client_request append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
      rewrite update_elections_data_client_request_leaderLogs. repeat find_rewrite.
      eauto.
    - do_in_map. subst. simpl in *.
      find_eapply_lem_hyp handleClientRequest_no_append_entries; eauto.
      contra.
  Qed.

  Lemma append_entries_came_from_leaders_timeout :
    refined_raft_net_invariant_timeout append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
      rewrite update_elections_data_timeout_leaderLogs. repeat find_rewrite.
      eauto.
    - do_in_map. subst. simpl in *.
      find_eapply_lem_hyp handleTimeout_packets; eauto.
      contra.
  Qed.

  Lemma append_entries_came_from_leaders_doLeader :
    refined_raft_net_invariant_do_leader append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
    - do_in_map. subst. simpl in *.
      find_eapply_lem_hyp doLeader_messages; eauto.
      repeat break_and.
      subst.
      find_eapply_lem_hyp leaders_have_leaderLogs_invariant; eauto.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
  Qed.
  

  Lemma append_entries_came_from_leaders_doGenericServer :
    refined_raft_net_invariant_do_generic_server append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - find_apply_hyp_hyp.
      break_exists.
      repeat find_higher_order_rewrite.
      update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
    - do_in_map. subst. simpl in *.
      find_eapply_lem_hyp doGenericServer_packets. subst. simpl in *. intuition.
  Qed.
  
  Lemma append_entries_came_from_leaders_reboot :
    refined_raft_net_invariant_reboot append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    subst. simpl in *. find_reverse_rewrite.
    find_apply_hyp_hyp. 
    repeat find_higher_order_rewrite.
    update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
  Qed.

  Lemma append_entries_came_from_leaders_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros.
    find_apply_hyp_hyp.
    find_apply_hyp_hyp. repeat find_higher_order_rewrite. eauto.
  Qed.

  Lemma append_entries_came_from_leaders_init :
    refined_raft_net_invariant_init append_entries_came_from_leaders.
  Proof.
    red. unfold append_entries_came_from_leaders. intros. simpl in *.
    intuition.
  Qed.
  
  Theorem append_entries_came_from_leaders_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      append_entries_came_from_leaders net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply append_entries_came_from_leaders_init.
    - apply append_entries_came_from_leaders_clientRequest.
    - apply append_entries_came_from_leaders_timeout.
    - apply append_entries_came_from_leaders_appendEntries.
    - apply append_entries_came_from_leaders_appendEntriesReply.
    - apply append_entries_came_from_leaders_requestVote.
    - apply append_entries_came_from_leaders_requestVoteReply.
    - apply append_entries_came_from_leaders_doLeader.
    - apply append_entries_came_from_leaders_doGenericServer.
    - apply append_entries_came_from_leaders_state_same_packet_subset.
    - apply append_entries_came_from_leaders_reboot.
  Qed.    

  Instance aercfli : append_entries_came_from_leaders_interface.
  split. exact append_entries_came_from_leaders_invariant.
  Qed.
  
End AppendEntriesRequestsCameFromLeaders.
