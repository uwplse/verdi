Require Import List.
Import ListNotations.
Require Import Nat.

Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import Raft.

Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import SortedInterface.
Require Import LogMatchingInterface.
Require Import StateMachineSafetyInterface.

Require Import MaxIndexSanityInterface.

Section MaxIndexSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {si : sorted_interface}.
  Context {smsi : state_machine_safety_interface}.
  Context {lmi : log_matching_interface}.

  Lemma maxIndex_sanity_init :
    raft_net_invariant_init maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_init, maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma handleClientRequest_lastApplied :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      lastApplied st' = lastApplied st.
  Proof.
    unfold handleClientRequest.
    intros.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleClientRequest_commitIndex :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      commitIndex st' = commitIndex st.
  Proof.
    unfold handleClientRequest.
    intros.
    repeat break_match; find_inversion; auto.
  Qed.

  Lemma handleClientRequest_maxIndex :
    forall h st client id c out st' l,
      handleClientRequest h st client id c = (out, st', l) ->
      sorted (log st') ->
      maxIndex (log st) <= maxIndex (log st').
  Proof.
    intros.
    destruct (log st') using (handleClientRequest_log_ind $(eauto)$).
    - auto.
    - simpl in *. break_and.
      destruct (log st); simpl in *.
      + omega.
      + find_insterU. conclude_using eauto. intuition.
  Qed.

  Lemma maxIndex_sanity_client_request :
    raft_net_invariant_client_request maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_client_request, maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; simpl in *; find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleClientRequest_lastApplied by eauto.
      find_apply_lem_hyp handleClientRequest_maxIndex.
      + eauto with *.
      + eapply handleClientRequest_logs_sorted; eauto.
        apply logs_sorted_invariant. auto.
    - erewrite handleClientRequest_commitIndex by eauto.
      find_apply_lem_hyp handleClientRequest_maxIndex.
      + eauto with *.
      + eapply handleClientRequest_logs_sorted; eauto.
        apply logs_sorted_invariant. auto.
  Qed.

  Lemma handleTimeout_lastApplied :
    forall h st out st' l,
      handleTimeout h st = (out, st', l) ->
      lastApplied st' = lastApplied st.
  Proof.
    unfold handleTimeout, tryToBecomeLeader; intros; repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma handleTimeout_commitIndex :
    forall h st out st' l,
      handleTimeout h st = (out, st', l) ->
      commitIndex st' = commitIndex st.
  Proof.
    unfold handleTimeout, tryToBecomeLeader; intros; repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma maxIndex_sanity_timeout :
    raft_net_invariant_timeout maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_timeout, maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; simpl in *; find_higher_order_rewrite; update_destruct; auto;
    erewrite handleTimeout_log_same by eauto.
    - erewrite handleTimeout_lastApplied; eauto.
    - erewrite handleTimeout_commitIndex; eauto.
  Qed.

  Lemma handleAppendEntries_lastApplied :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      lastApplied st' = lastApplied st.
  Proof.
    unfold handleAppendEntries, advanceCurrentTerm;
    intros; repeat break_match; repeat find_inversion; simpl; auto.
  Qed.

  Lemma sorted_maxIndex_app :
    forall l1 l2,
      sorted (l1 ++ l2) ->
      maxIndex l2 <= maxIndex (l1 ++ l2).
  Proof.
    induction l1; intros; simpl in *; intuition.
    destruct l2; intuition. simpl in *.
    specialize (H0 e). conclude H0 intuition. intuition.
  Qed.

  Lemma max_min_thing:
    forall a b c,
      a <= c ->
      max a (min b c) <= c.
  Proof.
    intros.
    destruct (max a (min b c)) using (Max.max_case _ _); intuition.
  Qed.
  
  Lemma maxIndex_sanity_append_entries :
    raft_net_invariant_append_entries maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_append_entries, maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intros.
    find_copy_apply_lem_hyp logs_sorted_invariant.
    unfold logs_sorted in *; break_and.
    find_copy_apply_lem_hyp state_machine_safety_invariant.
    intuition; simpl in *; find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleAppendEntries_lastApplied by eauto.
      find_copy_apply_lem_hyp handleAppendEntries_logs_sorted; auto using logs_sorted_invariant;
      try solve [repeat find_rewrite; intuition].
      match goal with
        | _ : handleAppendEntries ?h ?s ?t ?n ?pli ?plt ?es ?ci = (?s', ?m) |- _ =>
          pose proof handleAppendEntries_log_detailed
               h s t n pli plt es ci s' m
      end.
      intuition; repeat find_rewrite.
      + eauto.
      + subst.
        destruct (le_lt_dec (lastApplied (nwState net (pDst p)))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        find_copy_apply_lem_hyp log_matching_invariant.
        unfold log_matching, log_matching_hosts in *. intuition.
        match goal with
          | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
            specialize (H (pDst p) (maxIndex (log d))); forward H; intuition
        end.
        * find_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_nw in *.
          intuition.
          eapply_prop_hyp AppendEntries AppendEntries; intuition eauto.
          find_apply_lem_hyp maxIndex_non_empty.
          break_exists. intuition.
          find_apply_hyp_hyp. omega.
        * eapply le_trans; [|eauto]. omega.
        * break_exists. intuition.
          find_eapply_lem_hyp findAtIndex_None; eauto.
      + subst.
        destruct (le_lt_dec (lastApplied (nwState net (pDst p)))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.
        unfold state_machine_safety, state_machine_safety_nw in *.
        copy_eapply_prop_hyp In In; eauto;
        [|unfold commit_recorded; intuition; eauto; omega]. intuition.
        * subst.
          find_copy_apply_lem_hyp log_matching_invariant; eauto.
          omega.
        * destruct (log d); intuition. simpl in *.
          intuition; subst; auto.
          find_apply_hyp_hyp. omega.
      + destruct (le_lt_dec (lastApplied (nwState net (pDst p))) pli); intuition;
        [eapply le_trans; [| apply sorted_maxIndex_app]; auto;
         break_exists; intuition;
         erewrite maxIndex_removeAfterIndex; eauto|].
        destruct (le_lt_dec (lastApplied (nwState net (pDst p))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; intuition|]; [idtac].
        find_copy_apply_lem_hyp log_matching_invariant.
        unfold log_matching, log_matching_hosts in *. intuition.
        match goal with
          | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
            specialize (H (pDst p) (maxIndex es)); forward H; intuition
        end.
        * find_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_nw in *.
          intuition.
          eapply_prop_hyp AppendEntries AppendEntries; intuition eauto.
          find_apply_lem_hyp maxIndex_non_empty.
          break_exists. intuition.
          do 2 find_apply_hyp_hyp. omega.
        * eapply le_trans; [|eauto]. omega.
        * break_exists. intuition.
          match goal with
            | H : findAtIndex _ _ = None |- _ =>
              eapply findAtIndex_None with (x1 := x) in H
          end; eauto. congruence.
      + destruct (le_lt_dec (lastApplied (nwState net (pDst p))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; intuition|]; [idtac].
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.
        unfold state_machine_safety, state_machine_safety_nw in *.
        find_copy_apply_lem_hyp maxIndex_non_empty.
        break_exists. intuition.
        match goal with
          | _ : In ?x es, _ : maxIndex es = eIndex ?x |- _ =>
            assert (pli < eIndex x) by (eapply log_matching_invariant; eauto)
        end.
        copy_eapply_prop_hyp In In; eauto;
        [|unfold commit_recorded; intuition; eauto; omega]. intuition.
        * match goal with
            | H : _ = _ ++ _ |- _ => symmetry in H
          end.
          destruct es; intuition;
          simpl in *;
          intuition; subst_max; intuition;
          repeat clean;
          match goal with
            | _ : eIndex ?x' = eIndex ?x, H : context [eIndex ?x'] |- _ =>
              specialize (H x); conclude H ltac:(apply in_app_iff; auto)
          end; intuition.
    - find_copy_apply_lem_hyp handleAppendEntries_logs_sorted; auto using logs_sorted_invariant;
      try solve [repeat find_rewrite; intuition].
      match goal with
        | _ : handleAppendEntries ?h ?s ?t ?n ?pli ?plt ?es ?ci = (?s', ?m) |- _ =>
          pose proof handleAppendEntries_log_detailed
               h s t n pli plt es ci s' m
      end.
      intuition; repeat find_rewrite; try apply max_min_thing;
      match goal with
        | H : context [ lastApplied _ ] |- _ => clear H
      end.
      + eauto.
      + subst.
        destruct (le_lt_dec (commitIndex (nwState net (pDst p)))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        find_copy_apply_lem_hyp log_matching_invariant.
        unfold log_matching, log_matching_hosts in *. intuition.
        match goal with
          | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
            specialize (H (pDst p) (maxIndex (log d))); forward H; intuition
        end.
        * find_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_nw in *.
          intuition.
          eapply_prop_hyp AppendEntries AppendEntries; intuition eauto.
          find_apply_lem_hyp maxIndex_non_empty.
          break_exists. intuition.
          find_apply_hyp_hyp. omega.
        * eapply le_trans; [|eauto]. omega.
        * break_exists. intuition.
          find_eapply_lem_hyp findAtIndex_None; eauto.
      + subst.
        destruct (le_lt_dec (commitIndex (nwState net (pDst p)))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.
        unfold state_machine_safety, state_machine_safety_nw in *.
        copy_eapply_prop_hyp In In; eauto;
        [|unfold commit_recorded; intuition; eauto; omega]. intuition.
        * subst.
          find_copy_apply_lem_hyp log_matching_invariant; eauto.
          omega.
        * destruct (log d); intuition. simpl in *.
          intuition; subst; auto.
          find_apply_hyp_hyp. omega.
      + destruct (le_lt_dec (commitIndex (nwState net (pDst p))) pli); intuition;
        [eapply le_trans; [| apply sorted_maxIndex_app]; auto;
         break_exists; intuition;
         erewrite maxIndex_removeAfterIndex; eauto|].
        destruct (le_lt_dec (commitIndex (nwState net (pDst p))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; intuition|]; [idtac].
        find_copy_apply_lem_hyp log_matching_invariant.
        unfold log_matching, log_matching_hosts in *. intuition.
        match goal with
          | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
            specialize (H (pDst p) (maxIndex es)); forward H; intuition
        end.
        * find_apply_lem_hyp log_matching_invariant.
          unfold log_matching, log_matching_nw in *.
          intuition.
          eapply_prop_hyp AppendEntries AppendEntries; intuition eauto.
          find_apply_lem_hyp maxIndex_non_empty.
          break_exists. intuition.
          do 2 find_apply_hyp_hyp. omega.
        * eapply le_trans; [|eauto]. omega.
        * break_exists. intuition.
          match goal with
            | H : findAtIndex _ _ = None |- _ =>
              eapply findAtIndex_None with (x1 := x) in H
          end; eauto. congruence.
      + destruct (le_lt_dec (commitIndex (nwState net (pDst p))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; intuition|]; [idtac].
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.
        unfold state_machine_safety, state_machine_safety_nw in *.
        find_copy_apply_lem_hyp maxIndex_non_empty.
        break_exists. intuition.
        match goal with
          | _ : In ?x es, _ : maxIndex es = eIndex ?x |- _ =>
            assert (pli < eIndex x) by (eapply log_matching_invariant; eauto)
        end.
        copy_eapply_prop_hyp In In; eauto;
        [|unfold commit_recorded; intuition; eauto; omega]. intuition.
        * match goal with
            | H : _ = _ ++ _ |- _ => symmetry in H
          end.
          destruct es; intuition;
          simpl in *;
          intuition; subst_max; intuition;
          repeat clean;
          match goal with
            | _ : eIndex ?x' = eIndex ?x, H : context [eIndex ?x'] |- _ =>
              specialize (H x); conclude H ltac:(apply in_app_iff; auto)
          end; intuition.
  Qed.

  Lemma handleAppendEntriesReply_same_commitIndex :
    forall n st src t es b st' l,
      handleAppendEntriesReply n st src t es b = (st', l) ->
      commitIndex st' = commitIndex st.
  Proof.
    unfold handleAppendEntriesReply, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma maxIndex_sanity_append_entries_reply :
    raft_net_invariant_append_entries_reply maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_append_entries_reply,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleAppendEntriesReply_same_lastApplied by eauto.
      erewrite handleAppendEntriesReply_same_log by eauto.
      auto.
    - erewrite handleAppendEntriesReply_same_commitIndex by eauto.
      erewrite handleAppendEntriesReply_same_log by eauto.
      auto.
  Qed.

  Lemma handleRequestVote_same_commitIndex :
    forall n st t c li lt st' ms,
      handleRequestVote n st t c li lt = (st', ms) ->
      commitIndex st' = commitIndex st.
  Proof.
    unfold handleRequestVote, advanceCurrentTerm.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma maxIndex_sanity_request_vote :
    raft_net_invariant_request_vote maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_request_vote,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleRequestVote_same_log by eauto.
      erewrite handleRequestVote_same_lastApplied by eauto.
      auto.
    - erewrite handleRequestVote_same_log by eauto.
      erewrite handleRequestVote_same_commitIndex by eauto.
      auto.
  Qed.

  Lemma handleRequestVoteReply_same_commitIndex :
    forall n st src t v,
      commitIndex (handleRequestVoteReply n st src t v) = commitIndex st.
  Proof.
    unfold handleRequestVoteReply, advanceCurrentTerm.
    intros. repeat break_match; simpl; auto.
  Qed.

  Lemma maxIndex_sanity_request_vote_reply :
    raft_net_invariant_request_vote_reply maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_request_vote_reply,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_higher_order_rewrite; update_destruct; auto.
    - rewrite handleRequestVoteReply_same_log.
      rewrite handleRequestVoteReply_same_lastApplied.
      auto.
    - rewrite handleRequestVoteReply_same_log.
      rewrite handleRequestVoteReply_same_commitIndex.
      auto.
  Qed.

  Lemma doLeader_same_lastApplied :
    forall st n os st' ms,
      doLeader st n = (os, st', ms) ->
      lastApplied st' = lastApplied st.
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma fold_left_maximum_le' :
    forall l x y,
      x <= y ->
      x <= fold_left max l y.
  Proof.
    induction l; intros.
    - auto.
    - simpl. apply IHl. apply Max.max_case_strong; omega.
  Qed.

  Lemma fold_left_maximum_le :
    forall l x,
      x <= fold_left max l x.
  Proof.
    intros. apply fold_left_maximum_le'.
    auto.
  Qed.

  Lemma fold_left_maxmimum_increase_init :
    forall l x y,
      fold_left max l x = x ->
      x <= y ->
      fold_left max l y = y.
  Proof.
    induction l; intros.
    - auto.
    - simpl in *. revert H.
      repeat (apply Max.max_case_strong; intros).
      + eauto.
      + assert (a = y) by omega. subst_max. eauto.
      + subst x. pose proof (fold_left_maximum_le l a).
        assert (fold_left max l a = a) by omega.
        eauto.
      + subst x.
        pose proof (fold_left_maximum_le l a).
        assert (fold_left max l a = a) by omega.
        assert (a = y) by omega.
        subst. auto.
  Qed.

  Lemma fold_left_maximum_cases :
    forall l x,
      fold_left max l x = x \/
      exists y,
        In y l /\ fold_left max l x = y.
  Proof.
    induction l; simpl.
    - auto.
    - intros.
      specialize (IHl (max x a)).
      intuition.
      + revert H.
        apply Max.max_case_strong; intuition.
        intuition eauto using fold_left_maxmimum_increase_init.
      + break_exists. break_and. eauto.
  Qed.

  Lemma fold_left_maximum_ind :
    forall l x (P : nat -> Prop),
      P x ->
      (forall y, In y l -> P y) ->
      P (fold_left max l x).
  Proof.
    intros.
    destruct (fold_left_maximum_cases l x).
    - find_rewrite. auto.
    - break_exists. break_and. find_rewrite. eauto.
  Qed.

  Lemma doLeader_same_commitIndex :
    forall st n os st' ms,
      doLeader st n = (os, st', ms) ->
      sorted (log st) ->
      commitIndex st <= maxIndex (log st) ->
      commitIndex st' <= maxIndex (log st').
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl; auto;
    apply fold_left_maximum_ind; auto.
    - intros. do_in_map. find_apply_lem_hyp filter_In.
      subst. break_and.
      apply maxIndex_is_max; eauto using findGtIndex_in.
    - intros. do_in_map. find_apply_lem_hyp filter_In.
      break_and. subst.
      apply maxIndex_is_max; eauto using findGtIndex_in.
  Qed.

  Lemma maxIndex_sanity_do_leader :
    raft_net_invariant_do_leader maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_do_leader,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_higher_order_rewrite; update_destruct; auto.
    - erewrite doLeader_same_log by eauto.
      erewrite doLeader_same_lastApplied by eauto.
      auto.
    - erewrite doLeader_same_commitIndex; eauto.
      apply logs_sorted_invariant. auto.
  Qed.

  Lemma doGenericServer_lastApplied :
    forall h st out st' ms,
      doGenericServer h st = (out, st', ms) ->
      lastApplied st' = lastApplied st \/
      (lastApplied st < commitIndex st  /\
       lastApplied st' = commitIndex st).
  Proof.
    unfold doGenericServer.
    intros.
    repeat break_match; repeat find_inversion; simpl.
    - do_bool.
      revert Heqb.
      eapply applyEntries_spec_ind; eauto.
    - do_bool.
      revert Heqb.
      eapply applyEntries_spec_ind; eauto.
  Qed.


  Lemma doGenericServer_commitIndex :
    forall h st out st' ms,
      doGenericServer h st = (out, st', ms) ->
      commitIndex st' = commitIndex st.
  Proof.
    unfold doGenericServer.
    intros.
    repeat break_match; repeat find_inversion; simpl;
    eapply applyEntries_spec_ind; eauto.
  Qed.

  Lemma maxIndex_sanity_do_generic_server :
    raft_net_invariant_do_generic_server maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_do_generic_server,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_higher_order_rewrite; update_destruct; auto;
    erewrite doGenericServer_log by eauto.
    - find_apply_lem_hyp doGenericServer_lastApplied.
      intuition; find_rewrite; auto.
    - erewrite doGenericServer_commitIndex by eauto.
      auto.
  Qed.

  Lemma maxIndex_sanity_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_reverse_higher_order_rewrite; auto.
  Qed.

  Lemma maxIndex_sanity_reboot :
    raft_net_invariant_reboot maxIndex_sanity.
  Proof.
    unfold raft_net_invariant_reboot,
           maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    unfold reboot.
    intuition; find_higher_order_rewrite; update_destruct; auto with *.
  Qed.

  Lemma maxIndex_sanity_invariant :
    forall net,
      raft_intermediate_reachable net ->
      maxIndex_sanity net.
  Proof.
    intros.
    apply raft_net_invariant; auto.
    - apply maxIndex_sanity_init.
    - apply maxIndex_sanity_client_request.
    - apply maxIndex_sanity_timeout.
    - apply maxIndex_sanity_append_entries.
    - apply maxIndex_sanity_append_entries_reply.
    - apply maxIndex_sanity_request_vote.
    - apply maxIndex_sanity_request_vote_reply.
    - apply maxIndex_sanity_do_leader.
    - apply maxIndex_sanity_do_generic_server.
    - apply maxIndex_sanity_state_same_packet_subset.
    - apply maxIndex_sanity_reboot.
  Qed.

  Instance misi : max_index_sanity_interface.
  Proof.
    split.
    exact maxIndex_sanity_invariant.
  Qed.
End MaxIndexSanity.
