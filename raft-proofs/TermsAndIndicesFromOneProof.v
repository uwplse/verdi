Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import TermsAndIndicesFromOneInterface.
Require Import TermsAndIndicesFromOneLogInterface.

Section TermsAndIndicesFromOne.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rri : raft_refinement_interface}.
  Context {taifoli : terms_and_indices_from_one_log_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma terms_and_indices_from_one_vwl_init :
    refined_raft_net_invariant_init terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_init, terms_and_indices_from_one_vwl.
    simpl. contradiction.
  Qed.

  Lemma lifted_terms_and_indices_from_one_log : forall net h,
    refined_raft_intermediate_reachable net ->
    terms_and_indices_from_one (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ terms_and_indices_from_one_log_invariant).
    unfold terms_and_indices_from_one_log in *.
    rewrite <- deghost_spec with (net0 := net). auto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_client_request :
    refined_raft_net_invariant_client_request terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_client_request, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update;
      eauto using votesWithLog_update_elections_data_client_request.
  Qed.

  Lemma terms_and_indices_from_one_vwl_timeout :
    refined_raft_net_invariant_timeout terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_timeout, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_eapply_lem_hyp votesWithLog_update_elections_data_timeout; eauto.
    intuition; eauto. subst. find_apply_lem_hyp handleTimeout_log_same. find_rewrite.
    apply lifted_terms_and_indices_from_one_log; auto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_append_entries :
    refined_raft_net_invariant_append_entries terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_append_entries, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update;
      eauto using votesWithLog_update_elections_data_append_entries.
  Qed.

  Lemma terms_and_indices_from_one_vwl_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_request_vote :
    refined_raft_net_invariant_request_vote terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_request_vote, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_eapply_lem_hyp votesWithLog_update_elections_data_request_vote; eauto.
    intuition; eauto. subst. find_apply_lem_hyp handleRequestVote_log. find_rewrite.
    apply lifted_terms_and_indices_from_one_log; auto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; rewrite_update;
      eauto using votesWithLog_update_elections_data_request_vote_reply.
  Qed.

  Lemma terms_and_indices_from_one_vwl_do_leader :
    refined_raft_net_invariant_do_leader terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_do_leader, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    eapply H0. find_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_do_generic_server :
    refined_raft_net_invariant_do_generic_server terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    eapply H0. find_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, terms_and_indices_from_one_vwl.
    simpl. intuition. find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_reboot :
    refined_raft_net_invariant_reboot terms_and_indices_from_one_vwl.
  Proof.
    unfold refined_raft_net_invariant_reboot, terms_and_indices_from_one_vwl.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    eapply H0. find_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_vwl_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      terms_and_indices_from_one_vwl net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply terms_and_indices_from_one_vwl_init.
    - apply terms_and_indices_from_one_vwl_client_request.
    - apply terms_and_indices_from_one_vwl_timeout.
    - apply terms_and_indices_from_one_vwl_append_entries.
    - apply terms_and_indices_from_one_vwl_append_entries_reply.
    - apply terms_and_indices_from_one_vwl_request_vote.
    - apply terms_and_indices_from_one_vwl_request_vote_reply.
    - apply terms_and_indices_from_one_vwl_do_leader.
    - apply terms_and_indices_from_one_vwl_do_generic_server.
    - apply terms_and_indices_from_one_vwl_state_same_packet_subset.
    - apply terms_and_indices_from_one_vwl_reboot.
  Qed.

  Lemma terms_and_indices_from_one_ll_init :
    refined_raft_net_invariant_init terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_init, terms_and_indices_from_one_ll.
    simpl. contradiction.
  Qed.

  Lemma terms_and_indices_from_one_ll_client_request :
    refined_raft_net_invariant_client_request terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_client_request, terms_and_indices_from_one_ll.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_rewrite_lem update_elections_data_client_request_leaderLogs. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_timeout :
    refined_raft_net_invariant_timeout terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_timeout, terms_and_indices_from_one_ll.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_rewrite_lem update_elections_data_timeout_leaderLogs. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_append_entries :
    refined_raft_net_invariant_append_entries terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_append_entries, terms_and_indices_from_one_ll.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_rewrite_lem update_elections_data_appendEntries_leaderLogs. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, terms_and_indices_from_one_ll.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_request_vote :
    refined_raft_net_invariant_request_vote terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_request_vote, terms_and_indices_from_one_ll.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    simpl in *. find_rewrite_lem leaderLogs_update_elections_data_requestVote. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, terms_and_indices_from_one_ll.
    simpl. intuition. repeat find_higher_order_rewrite. update_destruct; rewrite_update; eauto.
    simpl in *. find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
    find_apply_lem_hyp handleRequestVoteReply_log.
    intuition; eauto; subst. find_rewrite.
    apply lifted_terms_and_indices_from_one_log; auto.
  Qed.

  Lemma terms_and_indices_from_one_ll_do_leader :
    refined_raft_net_invariant_do_leader terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_do_leader, terms_and_indices_from_one_ll.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    eapply H0. find_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_do_generic_server :
    refined_raft_net_invariant_do_generic_server terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, terms_and_indices_from_one_ll.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    eapply H0. find_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, terms_and_indices_from_one_ll.
    simpl. intuition. find_reverse_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_reboot :
    refined_raft_net_invariant_reboot terms_and_indices_from_one_ll.
  Proof.
    unfold refined_raft_net_invariant_reboot, terms_and_indices_from_one_ll.
    simpl. intuition. find_higher_order_rewrite. update_destruct; subst; rewrite_update; eauto.
    eapply H0. find_higher_order_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_ll_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      terms_and_indices_from_one_ll net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply terms_and_indices_from_one_ll_init.
    - apply terms_and_indices_from_one_ll_client_request.
    - apply terms_and_indices_from_one_ll_timeout.
    - apply terms_and_indices_from_one_ll_append_entries.
    - apply terms_and_indices_from_one_ll_append_entries_reply.
    - apply terms_and_indices_from_one_ll_request_vote.
    - apply terms_and_indices_from_one_ll_request_vote_reply.
    - apply terms_and_indices_from_one_ll_do_leader.
    - apply terms_and_indices_from_one_ll_do_generic_server.
    - apply terms_and_indices_from_one_ll_state_same_packet_subset.
    - apply terms_and_indices_from_one_ll_reboot.
  Qed.


  Instance taifoi : terms_and_indices_from_one_interface.
  Proof.
    constructor. split.
    - auto using terms_and_indices_from_one_vwl_invariant.
    - auto using terms_and_indices_from_one_ll_invariant.
  Qed.
End TermsAndIndicesFromOne.
