Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Require Import Raft.
Require Import SpecLemmas.

Require Import NoAppendEntriesToSelfInterface.

Section NoAppendEntriesToSelf.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma doLeader_no_messages_to_self :
    forall st h os st' ms m,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      fst m <> h.
  Proof.
    intros.
    unfold doLeader in *.
    repeat break_match; try solve [find_inversion; simpl in *; congruence].
    find_inversion.
    do_in_map.
    subst. simpl in *.
    find_apply_lem_hyp filter_In.
    intuition. subst.
    break_match; congruence.
  Qed.

  Lemma no_append_entries_to_self_do_leader :
    raft_net_invariant_do_leader no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    do_in_map.
    subst. simpl in *.
    find_eapply_lem_hyp doLeader_no_messages_to_self; eauto.
  Qed.

  Lemma no_append_entries_to_self_do_generic_server :
    raft_net_invariant_do_generic_server no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    do_in_map.
    subst. simpl in *.
    find_eapply_lem_hyp doGenericServer_packets. subst. simpl in *. intuition.
  Qed.

  Lemma no_append_entries_to_self_append_entries :
    raft_net_invariant_append_entries no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    subst. simpl in *. subst.
    find_apply_lem_hyp handleAppendEntries_not_append_entries.
    intuition. find_false. repeat eexists; eauto.
  Qed.
  
  Lemma no_append_entries_to_self_append_entries_reply :
    raft_net_invariant_append_entries_reply no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    do_in_map. subst. simpl in *.
    find_apply_lem_hyp handleAppendEntriesReply_packets.
    subst. intuition.
  Qed.
  
  Lemma no_append_entries_to_self_request_vote :
    raft_net_invariant_request_vote no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    subst. simpl in *. subst.
    find_apply_lem_hyp handleRequestVote_no_append_entries.
    intuition. find_false. repeat eexists; eauto.
  Qed.

  Lemma no_append_entries_to_self_request_vote_reply :
    raft_net_invariant_request_vote_reply no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
  Qed.

  Lemma no_append_entries_to_self_client_request :
    raft_net_invariant_client_request no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    do_in_map. subst. simpl in *.
    find_eapply_lem_hyp handleClientRequest_no_append_entries; eauto.
    intuition. find_false. repeat eexists; eauto.
  Qed.

  Lemma no_append_entries_to_self_timeout :
    raft_net_invariant_timeout no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    do_in_map. subst. simpl in *.
    find_eapply_lem_hyp handleTimeout_not_is_append_entries; eauto.
    intuition. find_false. repeat eexists; eauto.
  Qed.

  Lemma no_append_entries_to_self_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
  Qed.

  Lemma no_append_entries_to_self_reboot :
    raft_net_invariant_reboot no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *.
    find_reverse_rewrite. intuition eauto.
  Qed.

  Lemma no_append_entries_to_self_init :
    raft_net_invariant_init no_append_entries_to_self.
  Proof.
    red. red. intros. simpl in *. intuition.
  Qed.


  Theorem no_append_entries_to_self_invariant :
    forall net,
      raft_intermediate_reachable net ->
      no_append_entries_to_self net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply no_append_entries_to_self_init.
    - apply no_append_entries_to_self_client_request.
    - apply no_append_entries_to_self_timeout.
    - apply no_append_entries_to_self_append_entries.
    - apply no_append_entries_to_self_append_entries_reply.
    - apply no_append_entries_to_self_request_vote.
    - apply no_append_entries_to_self_request_vote_reply.
    - apply no_append_entries_to_self_do_leader.
    - apply no_append_entries_to_self_do_generic_server.
    - apply no_append_entries_to_self_state_same_packet_subset.
    - apply no_append_entries_to_self_reboot.
  Qed.    
  
  Instance noaetsi : no_append_entries_to_self_interface.
  split. exact no_append_entries_to_self_invariant.
  Qed.

End NoAppendEntriesToSelf.

