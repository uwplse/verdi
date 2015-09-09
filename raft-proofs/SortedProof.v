Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Omega.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.
Require Import CommonTheorems.

Require Import SpecLemmas.

Require Import TermSanityInterface.
Require Import SortedInterface.

Section SortedProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {tsi : term_sanity_interface}.

  Theorem logs_sorted_init :
    raft_net_invariant_init logs_sorted.
  Proof.
    unfold raft_net_invariant_init, logs_sorted,
    logs_sorted_host, logs_sorted_nw, packets_gt_prevIndex, packets_ge_prevTerm in *.
    intuition; simpl in *; intuition.
  Qed.

  Theorem handleClientRequest_packets :
    forall h st client id c out st' ps,
      handleClientRequest h st client id c = (out, st', ps) ->
      ps = [].
  Proof.
    intros. find_apply_lem_hyp handleClientRequest_log. intuition.
  Qed.

  Theorem logs_sorted_nw_packets_unchanged :
    forall net ps' st',
      logs_sorted_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ False) ->
      logs_sorted_nw (mkNetwork ps' st').
  Proof.
    unfold logs_sorted_nw in *. intros.
    simpl in *. find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem packets_gt_prevIndex_packets_unchanged :
    forall net ps' st',
      packets_gt_prevIndex net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ False) ->
      packets_gt_prevIndex (mkNetwork ps' st').
  Proof.
    unfold packets_gt_prevIndex in *. intros.
    simpl in *. find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem packets_ge_prevTerm_packets_unchanged :
    forall net ps' st',
      packets_ge_prevTerm net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ False) ->
      packets_ge_prevTerm (mkNetwork ps' st').
  Proof.
    unfold packets_ge_prevTerm in *. intros.
    simpl in *. find_apply_hyp_hyp. intuition eauto.
  Qed.

  Lemma handleClientRequest_logs_sorted :
    forall h client id c out st l net,
      handleClientRequest h (nwState net h) client id c = (out, st, l) ->
      raft_intermediate_reachable net ->
      logs_sorted_host net ->
      sorted (log st).
  Proof.
    unfold logs_sorted_host.
    intros.
    find_apply_lem_hyp handleClientRequest_log. intuition.
    + repeat find_rewrite. eauto.
    + find_apply_lem_hyp no_entries_past_current_term_invariant.
      break_exists; intuition; repeat find_rewrite.
      simpl. intuition eauto.
      * find_eapply_lem_hyp maxIndex_is_max; eauto.
        omega.
      * unfold no_entries_past_current_term, no_entries_past_current_term_host in *.
        intuition. simpl in *. find_apply_hyp_hyp. omega.
  Qed.

  Theorem logs_sorted_client_request :
    raft_net_invariant_client_request logs_sorted.
  Proof.
    unfold raft_net_invariant_client_request. unfold logs_sorted. intuition.
    - unfold logs_sorted_host in *. simpl in *. intros.
      find_higher_order_rewrite. break_match; eauto.
      subst.
      eauto using handleClientRequest_logs_sorted.
    - find_apply_lem_hyp handleClientRequest_packets. subst. simpl in *.
      eauto using logs_sorted_nw_packets_unchanged.
    - find_apply_lem_hyp handleClientRequest_packets. subst. simpl in *.
      eauto using packets_gt_prevIndex_packets_unchanged.
    - find_apply_lem_hyp handleClientRequest_packets. subst. simpl in *.
      eauto using packets_ge_prevTerm_packets_unchanged.
  Qed.

  Theorem handleTimeout_log :
    forall h st out st' ps,
      handleTimeout h st = (out, st', ps) ->
      log st' = log st.
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; find_inversion; subst; auto.
  Qed.

  Theorem logs_sorted_nw_only_new_packets_matter :
    forall net ps' l st',
      logs_sorted_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      logs_sorted_nw (mkNetwork l st') ->
      logs_sorted_nw (mkNetwork ps' st').
  Proof.
    unfold logs_sorted_nw. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem logs_sorted_nw_no_append_entries :
    forall net ps' l st',
      logs_sorted_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      (forall p, In p l -> ~ is_append_entries (pBody p)) ->
      logs_sorted_nw (mkNetwork ps' st').
  Proof.
    intros. eapply logs_sorted_nw_only_new_packets_matter; eauto.
    unfold logs_sorted_nw. intros. simpl in *. find_apply_hyp_hyp.
    exfalso. match goal with H : _ |- _ => apply H end.
    repeat eexists; eauto.
  Qed.

  Theorem logs_sorted_nw_not_append_entries :
    forall net ps' p' st',
      logs_sorted_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ p = p') ->
      ~ is_append_entries (pBody p') ->
      logs_sorted_nw (mkNetwork ps' st').
  Proof.
    intros.
    unfold logs_sorted_nw. intros. simpl in *. find_apply_hyp_hyp.
    intuition.
    - unfold logs_sorted_nw in *. eauto.
    - subst. exfalso. match goal with H : _ |- _ => apply H end.
      repeat eexists; eauto.
  Qed.

  Theorem packets_gt_prevIndex_only_new_packets_matter :
    forall net ps' l st',
      packets_gt_prevIndex net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      packets_gt_prevIndex (mkNetwork l st') ->
      packets_gt_prevIndex (mkNetwork ps' st').
  Proof.
    unfold packets_gt_prevIndex. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem packets_gt_prevIndex_no_append_entries :
    forall net ps' l st',
      packets_gt_prevIndex net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      (forall p, In p l -> ~ is_append_entries (pBody p)) ->
      packets_gt_prevIndex (mkNetwork ps' st').
  Proof.
    intros. eapply packets_gt_prevIndex_only_new_packets_matter; eauto.
    unfold packets_gt_prevIndex. intros. simpl in *. find_apply_hyp_hyp.
    exfalso. match goal with H : _ |- _ => apply H end.
    repeat eexists; eauto.
  Qed.

  Theorem packets_gt_prevIndex_not_append_entries :
    forall net ps' p' st',
      packets_gt_prevIndex net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ p = p') ->
      ~ is_append_entries (pBody p') ->
      packets_gt_prevIndex (mkNetwork ps' st').
  Proof.
    intros.
    unfold packets_gt_prevIndex. intros. simpl in *. find_apply_hyp_hyp.
    intuition.
    - unfold packets_gt_prevIndex in *. eauto.
    - subst. exfalso. match goal with H : _ |- _ => apply H end.
      repeat eexists; eauto.
  Qed.

  Theorem packets_ge_prevTerm_only_new_packets_matter :
    forall net ps' l st',
      packets_ge_prevTerm net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      packets_ge_prevTerm (mkNetwork l st') ->
      packets_ge_prevTerm (mkNetwork ps' st').
  Proof.
    unfold packets_ge_prevTerm. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem packets_ge_prevTerm_no_append_entries :
    forall net ps' l st',
      packets_ge_prevTerm net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      (forall p, In p l -> ~ is_append_entries (pBody p)) ->
      packets_ge_prevTerm (mkNetwork ps' st').
  Proof.
    intros. eapply packets_ge_prevTerm_only_new_packets_matter; eauto.
    unfold packets_ge_prevTerm. intros. simpl in *. find_apply_hyp_hyp.
    exfalso. match goal with H : _ |- _ => apply H end.
    repeat eexists; eauto.
  Qed.

  Theorem packets_ge_prevTerm_not_append_entries :
    forall net ps' p' st',
      packets_ge_prevTerm net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ p = p') ->
      ~ is_append_entries (pBody p') ->
      packets_ge_prevTerm (mkNetwork ps' st').
  Proof.
    intros.
    unfold packets_ge_prevTerm. intros. simpl in *. find_apply_hyp_hyp.
    intuition.
    - unfold packets_ge_prevTerm in *. eauto.
    - subst. exfalso. match goal with H : _ |- _ => apply H end.
      repeat eexists; eauto.
  Qed.

  Theorem handleTimeout_not_is_append_entries :
    forall h st st' ps p,
      handleTimeout h st = (st', ps) ->
      In p (send_packets h ps) -> ~ is_append_entries (pBody p).
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    break_match; find_inversion; subst; simpl in *; eauto;
    repeat (do_in_map; subst; simpl in *); intuition; break_exists; congruence.
  Qed.

  Theorem logs_sorted_timeout :
    raft_net_invariant_timeout logs_sorted.
  Proof.
    unfold raft_net_invariant_timeout. unfold logs_sorted. intuition.
    - unfold logs_sorted_host in *. simpl in *. intros.
      find_apply_lem_hyp handleTimeout_log.
      find_higher_order_rewrite. break_match; repeat find_rewrite; eauto.
    - eapply logs_sorted_nw_no_append_entries; eauto. intros.
      eauto using handleTimeout_not_is_append_entries.
    - eapply packets_gt_prevIndex_no_append_entries; eauto. intros.
      eauto using handleTimeout_not_is_append_entries.
    - eapply packets_ge_prevTerm_no_append_entries; eauto. intros.
      eauto using handleTimeout_not_is_append_entries.
  Qed.

  Ltac find_eapply_hyp_goal :=
    match goal with
      | H : _ |- _ =>
        eapply H
    end.

  Theorem sorted_append :
    forall l l',
      sorted l ->
      sorted l' ->
      (forall e e', In e l -> In e' l' -> eIndex e > eIndex e') ->
      (forall e e', In e l -> In e' l' -> eTerm e >= eTerm e') ->
      sorted (l ++ l').
  Proof.
    induction l; intros; simpl in *; auto.
    intuition; do_in_app; intuition; find_apply_hyp_hyp; intuition.
  Qed.

  Theorem sorted_index_term :
    forall l e e',
      eIndex e <= eIndex e' ->
      sorted l ->
      In e l ->
      In e' l ->
      eTerm e <= eTerm e'.
  Proof.
    induction l; intros; simpl in *; intuition; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma handleAppendEntries_logs_sorted :
    forall net p t n pli plt es ci st' m,
      raft_intermediate_reachable net ->
      logs_sorted net ->
      handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci =
      (st', m) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In p (nwPackets net) ->
      sorted (log st').
  Proof.
    intros. unfold logs_sorted in *. intuition.
    find_apply_lem_hyp handleAppendEntries_log. intuition.
    - find_rewrite; eauto.
    - subst. unfold logs_sorted_nw in *. simpl in *.
      find_eapply_hyp_goal; eauto.
    - find_rewrite. apply sorted_append; eauto using removeAfterIndex_sorted.
      + intros. find_apply_lem_hyp removeAfterIndex_In_le; eauto.
        unfold packets_gt_prevIndex in *.
        eapply gt_le_trans; [|eauto].
        find_eapply_hyp_goal; [in_crush|eauto|eauto].
        simpl in *. eauto.
      + intros. find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
        find_apply_lem_hyp removeAfterIndex_in.
        break_exists. intuition. subst.
        match goal with
          | H : eIndex ?x <= eIndex ?x', _ : In ?x ?ll |- _ =>
            apply sorted_index_term with (l := ll) (e := x) (e' := x') in H
        end; eauto.
        match goal with |- ?a >= ?b => cut (b <= a); [omega|] end.
        eapply le_trans; eauto.
        unfold packets_ge_prevTerm in *.
        find_eapply_hyp_goal; [in_crush|eauto|eauto];
        simpl in *; eauto.
  Qed.

  Theorem logs_sorted_append_entries :
    raft_net_invariant_append_entries logs_sorted.
  Proof.
    unfold raft_net_invariant_append_entries. intros. unfold logs_sorted. intuition.
    - unfold logs_sorted_host. simpl in *. intros.
      repeat find_higher_order_rewrite.
      break_match; repeat find_rewrite; eauto;
      [|unfold logs_sorted in *; intuition eauto].
      subst.
      eauto using handleAppendEntries_logs_sorted.
    - unfold logs_sorted in *. intuition.
      simpl in *.
      eapply logs_sorted_nw_not_append_entries; eauto.
      + intros. find_apply_hyp_hyp. intuition eauto.
      + simpl. eauto using handleAppendEntries_not_append_entries.
    - unfold logs_sorted in *. intuition.
      simpl in *.
      eapply packets_gt_prevIndex_not_append_entries; eauto.
      + intros. find_apply_hyp_hyp. intuition eauto.
      + simpl. eauto using handleAppendEntries_not_append_entries.
    - unfold logs_sorted in *. intuition.
      simpl in *.
      eapply packets_ge_prevTerm_not_append_entries; eauto.
      + intros. find_apply_hyp_hyp. intuition eauto.
      + simpl. eauto using handleAppendEntries_not_append_entries.
  Qed.

  Lemma handleAppendEntriesReply_log :
    forall h st from t es s st' ps,
      handleAppendEntriesReply h st from t es s = (st', ps) ->
      log st' = log st.
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Lemma handleAppendEntriesReply_packets :
    forall h st from t es s st' ps,
      handleAppendEntriesReply h st from t es s = (st', ps) ->
      ps = [].
  Proof.
    intros. unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Theorem logs_sorted_append_entries_reply :
    raft_net_invariant_append_entries_reply logs_sorted.
  Proof.
    unfold raft_net_invariant_append_entries_reply. unfold logs_sorted.
    intuition; simpl in *.
    - unfold logs_sorted_host in *. simpl in *. intros.
      find_apply_lem_hyp handleAppendEntriesReply_log.
      repeat find_higher_order_rewrite. break_match; try find_rewrite; eauto.
    - find_apply_lem_hyp handleAppendEntriesReply_packets. subst. simpl in *.
      eapply logs_sorted_nw_packets_unchanged; eauto.
      intros. find_apply_hyp_hyp. find_rewrite. in_crush.
    - find_apply_lem_hyp handleAppendEntriesReply_packets. subst. simpl in *.
      eapply packets_gt_prevIndex_packets_unchanged; eauto.
      intros. find_apply_hyp_hyp. find_rewrite. in_crush.
    - find_apply_lem_hyp handleAppendEntriesReply_packets. subst. simpl in *.
      eapply packets_ge_prevTerm_packets_unchanged; eauto.
      intros. find_apply_hyp_hyp. find_rewrite. in_crush.
  Qed.

  Lemma handleRequestVote_packets :
    forall h st t candidate lli llt st' m,
      handleRequestVote h st t candidate lli llt = (st', m) ->
      ~ is_append_entries m.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; find_inversion;
    subst; intuition; break_exists; congruence.
  Qed.

  Theorem logs_sorted_request_vote :
    raft_net_invariant_request_vote logs_sorted.
  Proof.
    unfold raft_net_invariant_request_vote. unfold logs_sorted.
    intuition; simpl in *.
    - unfold logs_sorted_host in *. simpl in *. intros.
      find_apply_lem_hyp handleRequestVote_log.
      repeat find_higher_order_rewrite. break_match; try find_rewrite; eauto.
    - find_apply_lem_hyp handleRequestVote_packets. subst. simpl in *.
      eapply logs_sorted_nw_not_append_entries; eauto.
      + intros. find_apply_hyp_hyp. find_rewrite. in_crush.
      + simpl. auto.
    - find_apply_lem_hyp handleRequestVote_packets. subst. simpl in *.
      eapply packets_gt_prevIndex_not_append_entries; eauto.
      + intros. find_apply_hyp_hyp. find_rewrite. in_crush.
      + simpl. auto.
    - find_apply_lem_hyp handleRequestVote_packets. subst. simpl in *.
      eapply packets_ge_prevTerm_not_append_entries; eauto.
      + intros. find_apply_hyp_hyp. find_rewrite. in_crush.
      + simpl. auto.
  Qed.

  Lemma handleRequestVoteReply_log :
    forall h st src t vg st',
      handleRequestVoteReply h st src t vg = st' ->
      log st' = log st.
  Proof.
    intros. unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; subst; auto.
  Qed.

  Theorem logs_sorted_request_vote_reply :
    raft_net_invariant_request_vote_reply logs_sorted.
  Proof.
    unfold raft_net_invariant_request_vote_reply. unfold logs_sorted.
    intuition; simpl in *.
    - unfold logs_sorted_host in *. simpl in *. intros.
      find_apply_lem_hyp handleRequestVoteReply_log.
      repeat find_higher_order_rewrite. break_match; try find_rewrite; eauto.
    - eauto using logs_sorted_nw_packets_unchanged.
    - eauto using packets_gt_prevIndex_packets_unchanged.
    - eauto using packets_ge_prevTerm_packets_unchanged.
  Qed.

  Lemma doLeader_log :
    forall h st os st' ps,
      doLeader st h = (os, st', ps) ->
      log st' = log st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Lemma doLeader_messages :
    forall h st os st' ms m t n pli plt entries c,
      doLeader st h = (os, st', ms) ->
      sorted (log st) ->
      In m ms ->
      snd m = AppendEntries t n pli plt entries c ->
      subseq entries (log st) /\
      (forall e, In e entries -> eIndex e > pli) /\
      (forall e, In e entries -> eTerm e >= plt).
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; subst; simpl in *; intuition.
    - unfold replicaMessage in *. do_in_map. simpl in *.
      subst. simpl in *. find_inversion.
      apply subseq_findGtIndex.
    - unfold replicaMessage in *. do_in_map. simpl in *.
      subst. simpl in *. find_inversion.
      find_apply_lem_hyp findGtIndex_necessary; intuition.
    - unfold replicaMessage in *. do_in_map. simpl in *.
      subst. simpl in *. find_inversion. break_match; intuition.
      find_apply_lem_hyp findGtIndex_necessary; intuition.
      find_apply_lem_hyp findAtIndex_elim. simpl in *.
      intuition. repeat find_rewrite.
      eapply sorted_index_term; eauto.
      omega.
  Qed.

  Theorem logs_sorted_do_leader :
    raft_net_invariant_do_leader logs_sorted.
  Proof.
    unfold raft_net_invariant_do_leader. unfold logs_sorted.
    intuition; simpl in *.
    - unfold logs_sorted_host in *. simpl in *. intros.
      find_apply_lem_hyp doLeader_log.
      repeat find_higher_order_rewrite. break_match; subst; try find_rewrite; eauto.
    - unfold logs_sorted_nw. intros. simpl in *.
      find_apply_hyp_hyp. intuition eauto.
      do_in_map. subst. simpl in *.
      find_eapply_lem_hyp doLeader_messages; intuition; eauto using sorted_subseq.
    - unfold packets_gt_prevIndex. intros. simpl in *.
      find_apply_hyp_hyp. intuition eauto.
      do_in_map. subst. simpl in *.
      find_eapply_lem_hyp doLeader_messages; [idtac|idtac|idtac|eauto];
      intuition eauto.
    - unfold packets_ge_prevTerm. intros. simpl in *.
      find_apply_hyp_hyp. intuition eauto.
      do_in_map. subst. simpl in *.
      find_eapply_lem_hyp doLeader_messages; [idtac|idtac|idtac|eauto];
      intuition eauto.
  Qed.

  Lemma doGenericServer_packets :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      ps = [].
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Theorem logs_sorted_do_generic_server :
    raft_net_invariant_do_generic_server logs_sorted.
  Proof.
    unfold raft_net_invariant_do_generic_server. unfold logs_sorted.
    intuition; simpl in *.
    - subst. unfold logs_sorted_host in *. simpl in *. intros.
      find_apply_lem_hyp doGenericServer_log.
      repeat find_higher_order_rewrite. break_match; try find_rewrite; eauto.
    - find_apply_lem_hyp doGenericServer_packets. subst. simpl in *.
      eauto using logs_sorted_nw_packets_unchanged.
    - find_apply_lem_hyp doGenericServer_packets. subst. simpl in *.
      eauto using packets_gt_prevIndex_packets_unchanged.
    - find_apply_lem_hyp doGenericServer_packets. subst. simpl in *.
      eauto using packets_ge_prevTerm_packets_unchanged.
  Qed.

  Theorem logs_sorted_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset logs_sorted.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset, logs_sorted.
    intuition; simpl in *.
    - unfold logs_sorted_host in *.
      intros. find_reverse_higher_order_rewrite. eauto.
    - eapply logs_sorted_nw_packets_unchanged with (st' := (nwState net')); eauto.
    - eapply packets_gt_prevIndex_packets_unchanged with (st' := (nwState net')); eauto.
    - eapply packets_ge_prevTerm_packets_unchanged with (st' := (nwState net')); eauto.
  Qed.

  Theorem logs_sorted_reboot :
    raft_net_invariant_reboot logs_sorted.
  Proof.
    unfold raft_net_invariant_reboot, logs_sorted, reboot.
    intuition; simpl in *.
    - unfold logs_sorted_host in *.
      intros. repeat find_higher_order_rewrite.
      simpl in *.
      break_match; subst; eauto.
    - subst. eapply logs_sorted_nw_packets_unchanged
             with (st' := nwState net') (ps' := nwPackets net') ; eauto.
      find_rewrite. intuition.
    - subst. eapply packets_gt_prevIndex_packets_unchanged
             with (st' := nwState net') (ps' := nwPackets net') ; eauto.
      find_rewrite. intuition.
    - subst. eapply packets_ge_prevTerm_packets_unchanged
             with (st' := nwState net') (ps' := nwPackets net') ; eauto.
      find_rewrite. intuition.
  Qed.

  Theorem logs_sorted_invariant :
    forall net,
      raft_intermediate_reachable net ->
      logs_sorted net.
  Proof.
    intros.
    eapply raft_net_invariant; eauto.
    - apply logs_sorted_init.
    - apply logs_sorted_client_request.
    - apply logs_sorted_timeout.
    - apply logs_sorted_append_entries.
    - apply logs_sorted_append_entries_reply.
    - apply logs_sorted_request_vote.
    - apply logs_sorted_request_vote_reply.
    - apply logs_sorted_do_leader.
    - apply logs_sorted_do_generic_server.
    - apply logs_sorted_state_same_packet_subset.
    - apply logs_sorted_reboot.
  Qed.

  Instance si : sorted_interface.
  Proof.
    split.
    eauto using handleAppendEntries_logs_sorted.
    eauto using handleClientRequest_logs_sorted.
    auto using logs_sorted_invariant.
  Qed.
End SortedProof.
