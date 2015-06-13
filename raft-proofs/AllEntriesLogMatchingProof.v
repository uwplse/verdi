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
Require Import RefinementCommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AllEntriesLeaderSublogInterface.
Require Import LeaderSublogInterface.
Require Import RefinedLogMatchingLemmasInterface.

Require Import AllEntriesLogMatchingInterface.

Section AllEntriesLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rri : raft_refinement_interface}.
  Context {aelsi : allEntries_leader_sublog_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac start :=
    red; unfold allEntries_log_matching; simpl; intros.

  Ltac start_update :=
    start;
    repeat find_higher_order_rewrite; do 2 (update_destruct; rewrite_update); [| | |eauto].

  Lemma allEntries_log_matching_init :
    refined_raft_net_invariant_init allEntries_log_matching.
  Proof.
    start. contradiction.
  Qed.

  Definition leader_sublog (net : network) :=
    forall leader e h,
      type (snd (nwState net leader)) = Leader ->
      In e (log (snd (nwState net h))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).

  Lemma leader_sublog_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_sublog net.
  Admitted.

  Lemma invalid_index :
    forall net h e,
      refined_raft_intermediate_reachable net ->
      In e (log (snd (nwState net h))) ->
      eIndex e = S (maxIndex (log (snd (nwState net h)))) ->
      False.
  Proof.
    intros.
    intro_refined_invariant entries_sorted_invariant.
    find_apply_lem_hyp maxIndex_is_max; auto.
    find_rewrite.
    omega.
  Qed.

  Lemma allEntries_log_matching_client_request :
    refined_raft_net_invariant_client_request allEntries_log_matching.
  Proof.
    start.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp update_elections_data_client_request_log_allEntries.
    intuition; simpl in *.
    - do 2 (update_destruct; rewrite_update); simpl in *; subst; repeat find_rewrite; eauto.
    - do 2 (update_destruct; rewrite_update); [| | |eauto]; simpl in *; subst;
        break_exists; break_and; repeat find_rewrite; subst; simpl in *.
      + intuition; subst; eauto; exfalso.
        * intro_refined_invariant allEntries_leader_sublog_invariant.
          eapply_prop_hyp allEntries_leader_sublog In; eauto.
          find_reverse_rewrite. concludes.
          repeat find_rewrite; eapply invalid_index; eauto.
        * repeat find_rewrite; eapply invalid_index; eauto.
      + intuition; subst; eauto; exfalso.
        intro_refined_invariant leader_sublog_invariant.
        eapply_prop_hyp leader_sublog In; eauto.
        find_rewrite. concludes.
        repeat find_rewrite; eapply invalid_index; eauto.
      + intuition; subst; eauto; exfalso.
        intro_refined_invariant allEntries_leader_sublog_invariant.
        eapply_prop_hyp allEntries_leader_sublog In; eauto.
        find_reverse_rewrite. concludes.
        repeat find_rewrite; eapply invalid_index; eauto.
  Qed.

  Lemma allEntries_log_matching_unchanged :
    forall net st' h gd d ps',
      allEntries_log_matching net ->
      (forall h' : Net.name, st' h' = update (nwState net) h (gd, d) h') ->
      log d = log (snd (nwState net h)) ->
      allEntries gd = allEntries (fst (nwState net h)) ->
      allEntries_log_matching {| nwPackets := ps'; nwState := st' |}.
  Proof.
    unfold allEntries_log_matching. intros.
    find_higher_order_rewrite.
    do 2 (update_destruct; rewrite_update); simpl in *;
      repeat find_rewrite; eauto.
  Qed.

  Ltac unchanged :=
    red; intros; eapply allEntries_log_matching_unchanged; subst; eauto.

  Lemma allEntries_log_matching_timeout :
    refined_raft_net_invariant_timeout allEntries_log_matching.
  Proof.
    unchanged.
    - eauto using handleTimeout_log_same.
    - apply update_elections_data_timeout_allEntries.
  Qed.

  Lemma appendEntries_haveNewEntries_false :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      haveNewEntries (snd (nwState net h)) es = false ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof.
    intros.
    unfold haveNewEntries in *. do_bool. intuition;
      [unfold not_empty in *; break_match; subst; simpl in *; intuition; congruence|].
    break_match; try congruence.
    do_bool. find_apply_lem_hyp findAtIndex_elim. intuition.
    assert (es <> nil) by (destruct es; subst; simpl in *; intuition; congruence).
    find_eapply_lem_hyp maxIndex_non_empty.
    break_exists. intuition.
    find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
    match goal with
      | H : In e es |- _ => copy_eapply maxIndex_is_max H; eauto
    end.
    repeat find_rewrite.
    find_eapply_lem_hyp entries_match_nw_host_invariant; eauto.
  Qed.

  Lemma allEntries_log_matching_append_entries :
    refined_raft_net_invariant_append_entries allEntries_log_matching.
  Proof.
    start_update.
    - subst. eapply update_elections_data_appendEntries_log_allEntries with (h' := n) in H.
      intuition; simpl in *.
      + repeat find_rewrite. eauto.
      + repeat find_rewrite. find_rewrite_lem map_app. find_apply_lem_hyp in_app_or.
        break_or_hyp; [|eauto].
        find_rewrite_lem map_of_map. simpl in *.
        find_rewrite_lem map_id.
        find_eapply_lem_hyp appendEntries_haveNewEntries_false; eauto.
        eapply uniqueIndices_elim_eq; eauto.
        apply sorted_uniqueIndices.
        intro_refined_invariant entries_sorted_invariant.
        auto.
      + subst. repeat find_rewrite.
        find_rewrite_lem map_app. find_apply_lem_hyp in_app_or.
        break_or_hyp.
        * find_rewrite_lem map_of_map. simpl in *. find_rewrite_lem map_id.
          eapply uniqueIndices_elim_eq; eauto.
          apply sorted_uniqueIndices.
          intro_refined_invariant entries_sorted_nw_invariant.
          eauto.
        * admit.
      + repeat find_rewrite.
        find_rewrite_lem map_app. do 2 find_apply_lem_hyp in_app_or.
        intuition.
        * find_rewrite_lem map_of_map. simpl in *. find_rewrite_lem map_id.
          eapply uniqueIndices_elim_eq; eauto.
          apply sorted_uniqueIndices.
          intro_refined_invariant entries_sorted_nw_invariant.
          eauto.
        * admit.
        * find_rewrite_lem map_of_map. simpl in *. find_rewrite_lem map_id.
          admit.
        * find_apply_lem_hyp removeAfterIndex_in. eauto.
    - admit.
    - admit.
  Admitted.

  Lemma allEntries_log_matching_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_log_matching.
  Proof.
    unchanged.
    eauto using handleAppendEntriesReply_log.
  Qed.

  Lemma allEntries_log_matching_request_vote :
    refined_raft_net_invariant_request_vote allEntries_log_matching.
  Proof.
    unchanged.
    - eauto using handleRequestVote_log.
    - apply update_elections_data_requestVote_allEntries.
  Qed.

  Lemma allEntries_log_matching_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_log_matching.
  Proof.
    unchanged.
    - eauto using handleRequestVoteReply_log.
    - apply update_elections_data_requestVoteReply_allEntries.
  Qed.

  Lemma allEntries_log_matching_do_leader :
    refined_raft_net_invariant_do_leader allEntries_log_matching.
  Proof.
  Admitted.

  Lemma allEntries_log_matching_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_log_matching.
  Proof.
  Admitted.

  Lemma allEntries_log_matching_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_log_matching.
  Proof.
  Admitted.

  Lemma allEntries_log_matching_reboot :
    refined_raft_net_invariant_reboot allEntries_log_matching.
  Proof.
  Admitted.

  Lemma allEntries_log_matching_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      allEntries_log_matching net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply allEntries_log_matching_init.
    - apply allEntries_log_matching_client_request.
    - apply allEntries_log_matching_timeout.
    - apply allEntries_log_matching_append_entries.
    - apply allEntries_log_matching_append_entries_reply.
    - apply allEntries_log_matching_request_vote.
    - apply allEntries_log_matching_request_vote_reply.
    - apply allEntries_log_matching_do_leader.
    - apply allEntries_log_matching_do_generic_server.
    - apply allEntries_log_matching_state_same_packet_subset.
    - apply allEntries_log_matching_reboot.
  Qed.


  Instance aelmi : allEntries_log_matching_interface.
  Proof.
    constructor. exact allEntries_log_matching_invariant.
  Qed.
End AllEntriesLogMatching.
