Require Import List.
Import ListNotations.

Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import MaxIndexSanityInterface.

Require Import CommitRecordedCommittedInterface.

Section CommitRecordedCommitted.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {misi : max_index_sanity_interface}.

  Definition commit_invariant (net : network (params := raft_refined_multi_params)) : Prop :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      (eIndex e <= lastApplied (snd (nwState net h)) \/
       eIndex e <= commitIndex (snd (nwState net h))) ->
      committed net e (currentTerm (snd (nwState net h))).

  Lemma commit_invariant_init :
    refined_raft_net_invariant_init commit_invariant.
  Proof.
    unfold refined_raft_net_invariant_init, commit_invariant.
    unfold commit_recorded_committed, commit_recorded, committed. simpl.
    intuition.
  Qed.

  Lemma handleClientRequest_currentTerm :
    forall h st client id c out st' ms,
      handleClientRequest h st client id c = (out, st', ms) ->
      currentTerm st' = currentTerm st.
  Proof.
    unfold handleClientRequest.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma handleClientRequest_commitIndex :
    forall h st client id c out st' ms,
      handleClientRequest h st client id c = (out, st', ms) ->
      commitIndex st' = commitIndex st.
  Proof.
    unfold handleClientRequest.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma directly_committed_allEntries_preserved :
    forall net net' e,
      directly_committed net e ->
      (forall h, In (eTerm e, e) (allEntries (fst (nwState net h))) ->
                 In (eTerm e, e) (allEntries (fst (nwState net' h)))) ->
      directly_committed net' e.
  Proof.
    unfold directly_committed.
    intuition.
    break_exists_exists.
    intuition.
  Qed.

  Lemma update_elections_data_client_request_allEntries :
    forall h st client id c out st' ms,
      handleClientRequest h (snd st) client id c = (out, st', ms) ->
      allEntries (update_elections_data_client_request h st client id c) =
      allEntries (fst st) \/
      (exists e : entry,
         eIndex e = S (maxIndex (log (snd st))) /\
         eTerm e = currentTerm (snd st) /\
         eClient e = client /\ eInput e = c /\ eId e = id /\ type (snd st) = Leader /\
         allEntries (update_elections_data_client_request h st client id c) =
         (currentTerm st', e) :: allEntries (fst st)).
  Proof.
    intros.
    unfold update_elections_data_client_request.
    repeat break_match; repeat find_inversion; auto.
    simpl.
    find_copy_apply_lem_hyp handleClientRequest_log.
    intuition.
    - repeat find_rewrite. do_bool. omega.
    - right.  break_exists_exists. intuition.
      congruence.
  Qed.

  Lemma update_elections_data_client_request_allEntries_ind :
    forall {h st client id c out st' ps},
      handleClientRequest h (snd st) client id c = (out, st', ps) ->
      forall (P : list (term * entry) -> Prop),
        P (allEntries (fst st)) ->
        (forall e,
         eIndex e = S (maxIndex (log (snd st))) ->
         eTerm e = currentTerm (snd st) ->
         eClient e = client -> eInput e = c -> eId e = id -> type (snd st) = Leader ->
         P ((currentTerm st', e) :: allEntries (fst st))) ->
        P (allEntries (update_elections_data_client_request h st client id c)).
  Proof.
    intros.
    find_apply_lem_hyp update_elections_data_client_request_allEntries.
    intuition.
    - find_rewrite. auto.
    - break_exists. intuition.
      repeat find_rewrite.  auto.
  Qed.

  Lemma update_elections_data_client_request_preserves_allEntries :
    forall h st client id c out st' ms t e,
      handleClientRequest h (snd st) client id c = (out, st', ms) ->
      In (t, e) (allEntries (fst st)) ->
      In (t, e) (allEntries (update_elections_data_client_request h st client id c)).
  Proof.
    intros.
    match goal with
      | [ |- context [ allEntries ?x ] ] =>
        destruct (allEntries x)
                 using (update_elections_data_client_request_allEntries_ind $(eauto)$)
    end; intuition.
  Qed.

  Lemma handleClientRequest_preservers_log :
    forall h st client id c out st' ms e,
      handleClientRequest h st client id c = (out, st', ms) ->
      In e (log st) ->
      In e (log st').
  Proof.
    intros.
    destruct (log st') using (handleClientRequest_log_ind $(eauto)$); intuition.
  Qed.

  Lemma committed_log_allEntries_preserved :
    forall net net' e t,
      committed net e t ->
      (forall h e',
         In e' (log (snd (nwState net h))) ->
         In e' (log (snd (nwState net' h)))) ->
      (forall h e' t',
         In (t', e') (allEntries (fst (nwState net h))) ->
         In (t', e') (allEntries (fst (nwState net' h)))) ->
      committed net' e t.
  Proof.
    unfold committed.
    intros.
    break_exists_exists.
    intuition.
    eapply directly_committed_allEntries_preserved; eauto.
  Qed.

  Lemma lifted_max_index_sanity :
    forall net h,
      refined_raft_intermediate_reachable net ->
      lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h))) /\
      commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ max_index_sanity_invariant).
    match goal with
      | [ H : _, H' : _ |- _ ] => apply H in H'; clear H
    end.
    unfold maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex in *.
    break_and.
    rewrite <- deghost_spec with (net0 := net). auto.
  Qed.

  Lemma commit_invariant_client_request :
    refined_raft_net_invariant_client_request commit_invariant.
  Proof.
    unfold refined_raft_net_invariant_client_request, commit_invariant.
    unfold commit_recorded_committed, commit_recorded.
    intros. simpl in *.
    repeat find_higher_order_rewrite.
    rewrite update_fun_comm with (f := snd).
    repeat match goal with H : _ |- _ => rewrite update_fun_comm with (f := snd) in H end.
    simpl in *.
    repeat match goal with
      | [H : _ |- _] => rewrite (update_fun_comm raft_data _) in H
    end.
    rewrite (update_fun_comm raft_data _).
    rewrite update_nop_ext' by (now erewrite <- handleClientRequest_currentTerm by eauto).
    match goal with
      | [H : _ |- _] => rewrite update_nop_ext' in H
          by (now erewrite <- handleClientRequest_lastApplied by eauto)
    end.
    match goal with
      | [H : _ |- _] => rewrite update_nop_ext' in H
          by (now erewrite <- handleClientRequest_commitIndex by eauto)
    end.
    update_destruct.
    - find_copy_apply_lem_hyp handleClientRequest_log.
      break_and. break_or_hyp.
      + repeat find_rewrite.
        eapply committed_log_allEntries_preserved; eauto.
        * simpl. intros. find_higher_order_rewrite.
          update_destruct; repeat find_rewrite; auto.
        * simpl. intros. find_higher_order_rewrite.
          update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
      + break_exists. break_and. repeat find_rewrite.
        simpl in *.
        match goal with
          | [ H : _ \/ In _ _ |- _ ] => invc H
        end.
        * find_eapply_lem_hyp (lifted_max_index_sanity net h0).
          break_and. simpl in *. omega.
        * { eapply committed_log_allEntries_preserved; eauto.
            - simpl. intros. find_higher_order_rewrite.
              update_destruct; repeat find_rewrite; auto.
              find_reverse_rewrite.
              eapply handleClientRequest_preservers_log; eauto.
            - simpl. intros. find_higher_order_rewrite.
              update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
          }
    - eapply committed_log_allEntries_preserved; eauto.
      + simpl. intros. find_higher_order_rewrite.
        update_destruct; repeat find_rewrite; eauto using handleClientRequest_preservers_log.
      + simpl. intros. find_higher_order_rewrite.
        update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
  Qed.

  Lemma commit_invariant_timeout :
    refined_raft_net_invariant_timeout commit_invariant.
  Admitted.

  Lemma commit_invariant_append_entries :
    refined_raft_net_invariant_append_entries commit_invariant.
  Admitted.

  Lemma commit_invariant_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply commit_invariant.
  Admitted.

  Lemma commit_invariant_request_vote :
    refined_raft_net_invariant_request_vote commit_invariant.
  Admitted.

  Lemma commit_invariant_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply commit_invariant.
  Admitted.

  Lemma commit_invariant_do_leader :
    refined_raft_net_invariant_do_leader commit_invariant.
  Admitted.

  Lemma commit_invariant_do_generic_server :
    refined_raft_net_invariant_do_generic_server commit_invariant.
  Admitted.

  Lemma commit_invariant_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset commit_invariant.
  Admitted.

  Lemma commit_invariant_reboot :
    refined_raft_net_invariant_reboot commit_invariant.
  Admitted.

  Theorem commit_recorded_committed_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      commit_invariant net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply commit_invariant_init.
    - apply commit_invariant_client_request.
    - apply commit_invariant_timeout.
    - apply commit_invariant_append_entries.
    - apply commit_invariant_append_entries_reply.
    - apply commit_invariant_request_vote.
    - apply commit_invariant_request_vote_reply.
    - apply commit_invariant_do_leader.
    - apply commit_invariant_do_generic_server.
    - apply commit_invariant_state_same_packet_subset.
    - apply commit_invariant_reboot.
  Qed.

  Instance crci : commit_recorded_committed_interface.
  Proof.
    split.
    intros.
    find_apply_lem_hyp commit_recorded_committed_invariant.
    unfold commit_invariant, commit_recorded_committed, commit_recorded in *.
    intros.
    find_rewrite_lem (deghost_spec net h).
    intuition.
  Qed.
End CommitRecordedCommitted.