Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LeadersHaveLeaderLogsStrongInterface.
Require Import SortedInterface.
Require Import LogMatchingInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import NextIndexSafetyInterface.

Section AppendEntriesRequestLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
  Context {rri : raft_refinement_interface}.
  Context {si : sorted_interface}.
  Context {lmi : log_matching_interface}.
  Context {nisi : nextIndex_safety_interface}.
  
  Theorem lift_sorted :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_sorted (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using logs_sorted_invariant.
  Qed.

  Theorem lift_logs_sorted :
    forall net h,
      refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    find_apply_lem_hyp lift_sorted.
    unfold logs_sorted, logs_sorted_host in *.
    intuition.
    unfold deghost in *. simpl in *. break_match; eauto.
  Qed.

  Theorem lift_log_matching :
    forall net,
      refined_raft_intermediate_reachable net ->
      log_matching (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using log_matching_invariant.
  Qed.
  
  Lemma update_elections_data_client_request_leaderLogs :
    forall h st client id c,
      leaderLogs (update_elections_data_client_request h st client id c) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_client_request in *.
    intros. repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma update_elections_data_timeout_leaderLogs :
    forall h st,
      leaderLogs (update_elections_data_timeout h st) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_timeout.
    intros.
    repeat break_match; simpl in *; auto.
  Qed.

  Lemma update_elections_data_appendEntries_leaderLogs :
    forall h st t h' pli plt es ci,
      leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) =
      leaderLogs (fst st).
  Proof.
    intros.
    unfold update_elections_data_appendEntries.
    repeat break_match; subst; simpl in *; auto.
  Qed.
  
  Lemma update_elections_data_requestVote_leaderLogs :
    forall h h' t lli llt st,
      leaderLogs (update_elections_data_requestVote h h' t h' lli llt st) =
      leaderLogs (fst st).
  Proof.
    unfold update_elections_data_requestVote.
    intros.
    repeat break_match; auto.
  Qed.

  Lemma update_elections_data_requestVoteReply_leaderLogs :
    forall h h' t  st t' ll' r,
      In (t', ll') (leaderLogs (fst st)) ->
      In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)).
  Proof.
    unfold update_elections_data_requestVoteReply.
    intros.
    repeat break_match; auto.
    simpl in *. intuition.
  Qed.

  Ltac update_destruct_hyp :=
    match goal with
    | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct :=
    match goal with
    | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.


  Ltac start :=
    red; unfold append_entries_leaderLogs; intros;
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
  
  Lemma append_entries_leaderLogs_appendEntries :
    refined_raft_net_invariant_append_entries append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        rewrite update_elections_data_appendEntries_leaderLogs; eauto;
        subst; auto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        rewrite update_elections_data_appendEntries_leaderLogs; eauto;
        subst; auto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        rewrite update_elections_data_appendEntries_leaderLogs; eauto;
        subst; auto.
      + eauto.
    - subst. simpl in *.
      unfold handleAppendEntries in *.
      repeat break_match; find_inversion; congruence.
  Qed.
  
  Lemma append_entries_leaderLogs_appendEntriesReply :
    refined_raft_net_invariant_append_entries_reply append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        subst; auto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        subst; auto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        subst; auto.
      + eauto.
    - do_in_map. subst. simpl in *.
      unfold handleAppendEntriesReply in *.
      repeat break_match; find_inversion; simpl in *; intuition.
  Qed.


  Lemma append_entries_leaderLogs_requestVote :
    refined_raft_net_invariant_request_vote append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        rewrite update_elections_data_requestVote_leaderLogs; eauto;
        subst; auto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        rewrite update_elections_data_requestVote_leaderLogs; eauto;
        subst; auto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto;
        rewrite update_elections_data_requestVote_leaderLogs; eauto;
        subst; auto.
      + eauto.
    - subst. simpl in *.
      unfold handleRequestVote in *.
      repeat break_match; find_inversion; congruence.
  Qed.
  
  Lemma append_entries_leaderLogs_requestVoteReply :
    refined_raft_net_invariant_request_vote_reply append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - prove_in. eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst; auto using update_elections_data_requestVoteReply_leaderLogs.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst; auto using update_elections_data_requestVoteReply_leaderLogs.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst; auto using update_elections_data_requestVoteReply_leaderLogs.
      + eauto.
  Qed.

  Lemma append_entries_leaderLogs_clientRequest :
    refined_raft_net_invariant_client_request append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. rewrite update_elections_data_client_request_leaderLogs.
        eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. rewrite update_elections_data_client_request_leaderLogs.
        eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. rewrite update_elections_data_client_request_leaderLogs.
        eauto.
      + eauto.
    - subst. simpl in *.
      unfold handleClientRequest in *.
      repeat break_match; find_inversion; do_in_map; simpl in *; intuition.
  Qed.
  
  Lemma append_entries_leaderLogs_timeout :
    refined_raft_net_invariant_timeout append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. rewrite update_elections_data_timeout_leaderLogs.
        eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. rewrite update_elections_data_timeout_leaderLogs.
        eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. rewrite update_elections_data_timeout_leaderLogs.
        eauto.
      + eauto.
    - subst. simpl in *.
      unfold handleTimeout, tryToBecomeLeader in *.
      repeat break_match; find_inversion; do_in_map; simpl in *; intuition;
      subst; simpl in *; do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma append_entries_leaderLogs_doGenericServer :
    refined_raft_net_invariant_do_generic_server append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
      + eauto.
    - unfold doGenericServer in *;
      repeat break_match; find_inversion; do_in_map; simpl in *; intuition;
      subst; simpl in *; do_in_map; subst; simpl in *; congruence.
  Qed.

  Require Import PeanoNat.
  Require Import Nat.

  Lemma doLeader_spec :
    forall st h os st' ms m t n pli plt es ci,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      t = currentTerm st /\
      log st' = log st /\
      type st = Leader /\
      ((pli = 0 /\ plt = 0 /\ es = findGtIndex (log st) 0) \/
       ((exists e, findAtIndex (log st) pli = Some e /\
              eTerm e = plt) /\
        es = findGtIndex (log st) pli) \/
       exists h', pred (getNextIndex st h') <> 0 /\ findAtIndex (log st) (pred (getNextIndex st h')) = None).
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    break_match; try solve [find_inversion; simpl in *; intuition].
    break_if; try solve [find_inversion; simpl in *; intuition].
    find_inversion. simpl. do_in_map. subst.
    simpl in *. find_inversion. intuition.
    match goal with
      | |- context [pred ?x] =>
        remember (pred x) as index
    end. break_match; simpl in *.
    - right. left. eauto.
    -  destruct index; intuition.
       right. right. exists x.
       match goal with
         | _ : S _ = pred ?x |- context [pred ?y] =>
           assert (pred x = pred y) by auto
       end.
       repeat find_rewrite. intuition.
  Qed.

  Lemma lift_nextIndex_safety :
    forall net,
      refined_raft_intermediate_reachable net ->
      nextIndex_safety (deghost net).
  Proof.
    intros.
    eapply lift_prop; eauto using nextIndex_safety_invariant.
  Qed.

  Require Import Omega.
  
  Lemma nextIndex_sanity :
    forall net h h',
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net h)) = Leader ->
      pred (getNextIndex (snd (nwState net h)) h') <> 0 ->
      exists e,
        findAtIndex (log (snd (nwState net h))) (pred (getNextIndex (snd (nwState net h)) h')) = Some e.
  Proof.
    intros.
    find_copy_apply_lem_hyp lift_log_matching.
    find_copy_apply_lem_hyp lift_nextIndex_safety.
    assert (pred (getNextIndex (snd (nwState net h)) h') > 0) by omega.
    unfold log_matching, log_matching_hosts in *.
    unfold nextIndex_safety in *.
    match goal with
      | H : forall _ _, type _ = _ -> _ |- _ => specialize (H h h')
    end. 
    intuition.
    match goal with
      | H : forall _ _, _ <= _ <= _ -> _ |- _ =>
        specialize (H h (pred (getNextIndex (snd (nwState net h)) h')))
    end.
    unfold raft_refined_base_params in *.
    repeat find_rewrite_lem deghost_spec. intuition.
    break_exists_exists. intuition.
    apply findAtIndex_intro; eauto using lift_logs_sorted, sorted_uniqueIndices.
  Qed.

  Lemma sorted_findGtIndex_0 :
    forall l,
      (forall e, In e l -> eIndex e > 0) ->
      sorted l ->
      findGtIndex l 0 = l.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; intuition.
    - f_equal. auto.
    - do_bool. specialize (H a); intuition; omega.
  Qed.

  Lemma entries_gt_0 :
    forall net h e,
      refined_raft_intermediate_reachable net ->
      In e (log (snd (nwState net h))) ->
      eIndex e > 0.
  Proof.
    intros.
    find_apply_lem_hyp lift_log_matching.
    unfold log_matching, log_matching_hosts in *. intuition.
    unfold raft_refined_base_params in *.
    match goal with
      | H : In _ _ |- _ =>
        rewrite <- deghost_spec in H
    end. eauto.
  Qed.
  
  Lemma Prefix_refl :
    forall A (l : list A),
      Prefix l l.
  Proof.
    intros. induction l; simpl in *; auto.
  Qed.

  Require Import Omega.
  
  Lemma findGtIndex_app_in_1 :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      In e l1 ->
      exists l',
        findGtIndex (l1 ++ l2) (eIndex e) = l' /\
        forall x,
          In x l' -> In x l1.
  Proof.
    induction l1; intros; simpl in *; intuition.
    - subst. break_if; do_bool; try omega.
      eexists; repeat (simpl in *; intuition).
    - specialize (H1 e); intuition. conclude H1 ltac:(apply in_app_iff; intuition).
      break_if; do_bool; try omega. eexists; intuition; eauto.
      simpl in *. intuition.
      eapply_prop_hyp sorted sorted; eauto. break_exists; intuition.
  Qed.

  Lemma sorted_app_in_1 :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      eIndex e > 0 ->
      In e l1 ->
      eIndex e > maxIndex l2.
  Proof.
    induction l1; intros; simpl in *; intuition.
    subst. destruct l2; simpl in *; auto.
    specialize (H2 e0); concludes; intuition.
  Qed.

  Lemma findGtIndex_Prefix :
    forall l i,
      Prefix (findGtIndex l i) l.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; simpl in *; intuition.
  Qed.
  
  Lemma findGtIndex_app_in_2 :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      In e l2 ->
      exists l',
        findGtIndex (l1 ++ l2) (eIndex e) = l1 ++ l' /\
        Prefix l' l2.
  Proof.
    induction l1; intros; simpl in *; intuition.
    - eexists; intuition eauto using findGtIndex_Prefix.
    - break_if; simpl in *; intuition.
      + eapply_prop_hyp sorted sorted; eauto.
        break_exists; intuition; find_rewrite; eauto.
      + do_bool. specialize (H1 e); conclude H1 ltac:(apply in_app_iff; intuition).
        omega.
  Qed.

  Lemma findGtIndex_app_eq :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      In e l2 ->
      findGtIndex (l1 ++ l2) (eIndex e) = l1 ->
      eIndex e = maxIndex l2.
  Proof.
    induction l1; intros; simpl in *.
    - destruct l2; simpl in *; intuition; subst; auto.
      break_if; try congruence. do_bool.
      find_apply_hyp_hyp. intuition.
    - simpl in *. break_if; try congruence.
      do_bool. find_inversion. intuition.
  Qed.
      
  
  Lemma append_entries_leaderLogs_doLeader :
    refined_raft_net_invariant_do_leader append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    subst. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
    - eapply_prop_hyp In In; break_exists. intuition; eauto.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
      + repeat eexists; intuition eauto.
        repeat find_higher_order_rewrite.
        update_destruct; subst_max; rewrite_update; simpl in *; eauto.
        subst. replace gd with (fst (nwState net x)); eauto; repeat find_rewrite; reflexivity.
      + eauto.
    - do_in_map. subst.
      assert (sorted (log (snd (nwState net h)))) by eauto using lift_logs_sorted.
      assert (forall e, In e (log (snd (nwState net h))) -> eIndex e > 0) by eauto using entries_gt_0.
      simpl in *.
      find_eapply_lem_hyp doLeader_spec; [|eauto|eauto]. intuition.
      + subst.
        match goal with
          | H : doLeader ?d ?h = _, H' : type ?d = _ |- _ =>
            replace d with (snd (nwState net h)) in H by (repeat find_rewrite; reflexivity);
            replace d with (snd (nwState net h)) in H' by (repeat find_rewrite; reflexivity)
        end.
        find_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
        exists h.
        break_exists_exists. repeat find_rewrite. 
        eexists; intuition eauto using Prefix_refl; auto.
        * simpl in *. repeat find_rewrite.
          eapply sorted_findGtIndex_0; eauto.
        * simpl in *. repeat find_higher_order_rewrite. rewrite_update. eauto.
      + subst. break_exists. intuition.
        find_apply_lem_hyp findAtIndex_elim. intuition. subst.
        match goal with
          | H : doLeader ?d ?h = _, H' : type ?d = _, H'' : context [log ?d] |- _ =>
            replace d with (snd (nwState net h)) in H by (repeat find_rewrite; reflexivity);
            replace d with (snd (nwState net h)) in H' by (repeat find_rewrite; reflexivity);
            replace d with (snd (nwState net h)) in H'' by (repeat find_rewrite; reflexivity);
            replace d with (snd (nwState net h)) by (repeat find_rewrite; reflexivity)
        end.
        find_copy_apply_lem_hyp lift_log_matching.
        unfold log_matching, log_matching_hosts in *. intuition.
        match goal with
          | H : forall _ _, In _ _ -> _ |- _ =>
            specialize (H h x0);
              conclude H ltac:(unfold deghost in *;
                                repeat (break_match; simpl in *);
                               repeat (simpl in *; find_rewrite);
                               auto)
        end.
        find_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
        exists h.
        break_exists. intuition. exists x1.
        repeat (find_rewrite; simpl in *).
        do_in_app. intuition.
        * find_copy_eapply_lem_hyp findGtIndex_app_in_1; eauto.
          break_exists_exists. exists nil.
          ii; simpl in *; auto; eauto using sorted_app_in_1;
          [rewrite app_nil_r; auto|].
          find_higher_order_rewrite. rewrite_update.
          simpl in *. auto.
        * { find_copy_eapply_lem_hyp findGtIndex_app_in_2; eauto.
            exists x2. break_exists_exists.
            ii; simpl in *; auto; intuition eauto.
            - find_higher_order_rewrite. rewrite_update. auto.
            - right. left. eexists; intuition; eauto.
              match goal with
                  | |- Prefix_sane ?l _ _ =>
                    unfold Prefix_sane; destruct l; intuition
              end;
                try rewrite app_nil_r in *; eauto using findGtIndex_app_eq.
          }
      + exfalso.
        break_exists. ii; subst.
        replace d with (snd (nwState net h)) in * by (repeat find_rewrite; reflexivity).
        find_eapply_lem_hyp nextIndex_sanity; eauto. break_exists. congruence.
  Qed.

  Lemma append_entries_leaderLogs_init :
    refined_raft_net_invariant_init append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs, step_m_init.
    intros. simpl in *. intuition.
  Qed.

  Lemma append_entries_leaderLogs_state_same_packets_subset :
    refined_raft_net_invariant_state_same_packet_subset append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    find_apply_hyp_hyp. eapply_prop_hyp In In; eauto.
    break_exists_exists; ii; eauto;
    repeat find_reverse_higher_order_rewrite; eauto.
  Qed.

  Lemma append_entries_leaderLogs_reboot :
    refined_raft_net_invariant_reboot append_entries_leaderLogs.
  Proof.
    red. unfold append_entries_leaderLogs. intros.
    repeat find_rewrite.
    eapply_prop_hyp In In; eauto.
    break_exists_exists; ii; eauto;
    repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update;
    simpl in *; repeat find_rewrite; auto.
  Qed.

  Theorem append_entries_leaderLogs_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      append_entries_leaderLogs net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply append_entries_leaderLogs_init.
    - apply append_entries_leaderLogs_clientRequest.
    - apply append_entries_leaderLogs_timeout.
    - apply append_entries_leaderLogs_appendEntries.
    - apply append_entries_leaderLogs_appendEntriesReply.
    - apply append_entries_leaderLogs_requestVote.
    - apply append_entries_leaderLogs_requestVoteReply.
    - apply append_entries_leaderLogs_doLeader.
    - apply append_entries_leaderLogs_doGenericServer.
    - apply append_entries_leaderLogs_state_same_packets_subset.
    - apply append_entries_leaderLogs_reboot.
  Qed.

  Instance aerlli : append_entries_leaderLogs_interface.
  split. exact append_entries_leaderLogs_invariant.
  Qed.

End AppendEntriesRequestLeaderLogs.
