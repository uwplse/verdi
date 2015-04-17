Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import TermsAndIndicesFromOneLogInterface.
Require Import CurrentTermGtZeroInterface.

Section TermsAndIndicesFromOneLog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {ctgzi : current_term_gt_zero_interface}.

  Definition terms_and_indices_from_one_log_nw (net : network) : Prop :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      terms_and_indices_from_one entries.

  Definition terms_and_indices_from_one_log_ind (net : network) : Prop :=
    terms_and_indices_from_one_log net /\ terms_and_indices_from_one_log_nw net.

  Lemma terms_and_indices_from_one_log_ind_init :
    raft_net_invariant_init terms_and_indices_from_one_log_ind.
  Proof.
    split.
    - unfold terms_and_indices_from_one_log, terms_and_indices_from_one. simpl. contradiction.
    - unfold terms_and_indices_from_one_log_nw, terms_and_indices_from_one. simpl. contradiction.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma taifol_no_append_entries :
    forall ps' net ms p t leaderId prevLogIndex prevLogTerm entries leaderCommit h,
      (forall (p : packet), In p ps' -> In p (nwPackets net) \/ In p (send_packets h ms)) ->
      (forall m, In m ms -> ~ is_append_entries (snd m)) ->
      In p ps' ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      terms_and_indices_from_one_log_nw net ->
      terms_and_indices_from_one entries.
  Proof.
    intros. find_apply_hyp_hyp. break_or_hyp; eauto. unfold send_packets in *. do_in_map.
    find_apply_hyp_hyp. unfold not in *. find_false.
    subst. simpl in *. repeat find_rewrite. eauto 10.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_client_request :
    raft_net_invariant_client_request terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp handleClientRequest_log. intuition.
      + repeat find_rewrite. auto.
      + break_exists. intuition.
        unfold terms_and_indices_from_one_log, terms_and_indices_from_one in *.
        intros. repeat find_rewrite. simpl in *. break_or_hyp.
        * intuition. find_apply_lem_hyp current_term_gt_zero_invariant. find_rewrite.
          eapply_prop current_term_gt_zero. congruence.
        * eauto.
    - eapply taifol_no_append_entries; eauto using handleClientRequest_no_append_entries.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_timeout :
    raft_net_invariant_timeout terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp handleTimeout_log_same. find_rewrite. auto.
    - eapply taifol_no_append_entries; eauto using handleTimeout_packets.
  Qed.

  Lemma terms_and_indices_from_one_app :
    forall xs ys,
      terms_and_indices_from_one xs ->
      terms_and_indices_from_one ys ->
      terms_and_indices_from_one (xs ++ ys).
  Proof.
    induction xs.
    - auto.
    - unfold terms_and_indices_from_one in *. simpl. intros. break_or_hyp; eauto.
  Qed.

  Lemma terms_and_indices_from_one_In :
    forall (xs ys : list entry),
      (forall x, In x xs -> In x ys) ->
      terms_and_indices_from_one ys ->
      terms_and_indices_from_one xs.
  Proof.
    unfold terms_and_indices_from_one. eauto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_append_entries :
    raft_net_invariant_append_entries terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp handleAppendEntries_log. intuition.
      + find_rewrite. auto.
      + subst. unfold terms_and_indices_from_one_log_nw in *. eauto.
      + break_exists. intuition. subst. find_rewrite. apply terms_and_indices_from_one_app.
        * eauto.
        * eapply terms_and_indices_from_one_In; [eapply removeAfterIndex_in | eauto].
    - unfold terms_and_indices_from_one_log_nw in *. find_apply_hyp_hyp. intuition; eauto.
      find_apply_lem_hyp handleAppendEntries_not_append_entries.
      exfalso. apply H. repeat eexists. subst. eauto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_append_entries_reply :
    raft_net_invariant_append_entries_reply terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp handleAppendEntriesReply_log. find_rewrite. auto.
    - find_apply_hyp_hyp. intuition; eauto. do_in_map.
      find_apply_lem_hyp handleAppendEntriesReply_packets; eauto. subst. contradiction.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_request_vote :
    raft_net_invariant_request_vote terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp handleRequestVote_log. find_rewrite. auto.
    - find_apply_hyp_hyp. intuition; eauto. find_apply_lem_hyp handleRequestVote_no_append_entries.
      unfold not in *. find_false. repeat eexists. subst. eauto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_request_vote_reply :
    raft_net_invariant_request_vote_reply terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; rewrite_update; auto.
      symmetry in H. find_apply_lem_hyp handleRequestVoteReply_log. subst. find_rewrite. auto.
    - eauto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_do_leader :
    raft_net_invariant_do_leader terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp doLeader_log. find_rewrite. auto.
    - find_apply_hyp_hyp. intuition; eauto.
      unfold doLeader in *. repeat break_match; tuple_inversion; subst; try contradiction.
      repeat do_in_map. unfold replicaMessage in *. subst. simpl in *. find_inversion.
      eapply terms_and_indices_from_one_In. apply findGtIndex_in. auto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_do_generic_server :
    raft_net_invariant_do_generic_server terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      find_apply_lem_hyp doGenericServer_log. find_rewrite. auto.
    - find_apply_lem_hyp doGenericServer_packets. find_apply_hyp_hyp. subst. intuition; eauto.
      do_in_map. contradiction.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_reverse_higher_order_rewrite. auto.
    - eauto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_reboot :
    raft_net_invariant_reboot terms_and_indices_from_one_log_ind.
  Proof.
    red. unfold terms_and_indices_from_one_log_ind. split; red; simpl in *; intuition.
    - find_higher_order_rewrite. update_destruct; subst; rewrite_update; auto.
      unfold reboot. eauto.
    - find_reverse_rewrite. eauto.
  Qed.

  Lemma terms_and_indices_from_one_log_ind_invariant :
    forall net,
      raft_intermediate_reachable net ->
      terms_and_indices_from_one_log_ind net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply terms_and_indices_from_one_log_ind_init.
    - apply terms_and_indices_from_one_log_ind_client_request.
    - apply terms_and_indices_from_one_log_ind_timeout.
    - apply terms_and_indices_from_one_log_ind_append_entries.
    - apply terms_and_indices_from_one_log_ind_append_entries_reply.
    - apply terms_and_indices_from_one_log_ind_request_vote.
    - apply terms_and_indices_from_one_log_ind_request_vote_reply.
    - apply terms_and_indices_from_one_log_ind_do_leader.
    - apply terms_and_indices_from_one_log_ind_do_generic_server.
    - apply terms_and_indices_from_one_log_ind_state_same_packet_subset.
    - apply terms_and_indices_from_one_log_ind_reboot.
  Qed.

  Instance taifoli : terms_and_indices_from_one_log_interface.
  Proof.
    split. apply terms_and_indices_from_one_log_ind_invariant.
  Qed.
End TermsAndIndicesFromOneLog.
