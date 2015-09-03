Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import NoAppendEntriesRepliesToSelfInterface.

Require Import MatchIndexLeaderInterface.

Section MatchIndexLeader.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {naertsi : no_append_entries_replies_to_self_interface}.

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
  
  Lemma match_index_leader_append_entries_reply :
    raft_net_invariant_append_entries_reply match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_eapply_lem_hyp handleAppendEntriesReply_matchIndex_leader_preserved; eauto.
    erewrite handleAppendEntriesReply_log; eauto.
    intuition.
    find_apply_hyp_hyp.
    find_higher_order_rewrite; auto.
    find_apply_lem_hyp no_append_entries_replies_to_self_invariant.
    unfold no_append_entries_replies_to_self in *.
    intuition.
    match goal with
      | H : context [_ = _ -> False] |- _ => eapply H
    end; eauto.
  Qed.

  Lemma match_index_leader_client_request :
    raft_net_invariant_client_request match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleClientRequest_type.
    find_eapply_lem_hyp handleClientRequest_matchIndex_maxIndex.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma match_index_leader_request_vote_reply :
    raft_net_invariant_request_vote_reply match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleRequestVoteReply_matchIndex.
    intuition; repeat find_rewrite; eauto.
    erewrite handleRequestVoteReply_log; eauto.
  Qed.

  Lemma match_index_leader_append_entries :
    raft_net_invariant_append_entries match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleAppendEntries_matchIndex_preserved.
    unfold matchIndex_preserved in *.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma match_index_leader_request_vote :
    raft_net_invariant_request_vote match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleRequestVote_matchIndex_preserved.
    unfold matchIndex_preserved in *.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma match_index_leader_timeout :
    raft_net_invariant_timeout match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp handleTimeout_matchIndex_preserved.
    unfold matchIndex_preserved in *.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma match_index_leader_do_leader :
    raft_net_invariant_do_leader match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp doLeader_matchIndex_preserved.
    unfold matchIndex_preserved in *.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma match_index_leader_do_generic_server :
    raft_net_invariant_do_generic_server match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto.
    find_copy_apply_lem_hyp doGenericServer_matchIndex_preserved.
    unfold matchIndex_preserved in *.
    intuition; repeat find_rewrite; eauto.
  Qed.

  Lemma match_index_leader_reboot :
    raft_net_invariant_reboot match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *; eauto. congruence.
  Qed.

  Lemma match_index_leader_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. intros.
    repeat find_reverse_higher_order_rewrite; eauto.
  Qed.

  Lemma match_index_leader_init :
    raft_net_invariant_init match_index_leader.
  Proof.
    red. unfold match_index_leader in *. simpl in *. congruence.
  Qed.
  
  Instance mili : match_index_leader_interface.
  split.
  intros. apply raft_net_invariant; auto.
  - exact match_index_leader_init.
  - exact match_index_leader_client_request.
  - exact match_index_leader_timeout.
  - exact match_index_leader_append_entries.
  - exact match_index_leader_append_entries_reply.
  - exact match_index_leader_request_vote.
  - exact match_index_leader_request_vote_reply.
  - exact match_index_leader_do_leader.
  - exact match_index_leader_do_generic_server.
  - exact match_index_leader_state_same_packet_subset.
  - exact match_index_leader_reboot.
  Qed.
End MatchIndexLeader.
