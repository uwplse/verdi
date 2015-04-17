Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.


Require Import LogsLeaderLogsInterface.
Require Import LeaderLogsSortedInterface.
Require Import LeaderLogsContiguousInterface.
Require Import LeaderLogsLogMatchingInterface.
Require Import RefinedLogMatchingLemmasInterface.
Require Import LeadersHaveLeaderLogsStrongInterface.
Require Import NextIndexSafetyInterface.
Require Import SortedInterface.

Section LogsLeaderLogs.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {llsi : leaderLogs_sorted_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {llci : leaderLogs_contiguous_interface}.
  Context {lllmi : leaderLogs_entries_match_interface}.
  Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
  Context {nisi : nextIndex_safety_interface}.
  Context {si : sorted_interface}.

  Definition logs_leaderLogs_nw_weak net :=
    forall p t n pli plt es ci e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e es ->
      exists leader ll es' ll',
        In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\
        Prefix ll' ll /\
        removeAfterIndex es (eIndex e) = es' ++ ll' /\
        (forall e', In e' es' -> eTerm e' = eTerm e).

  Lemma logs_leaderLogs_nw_weaken :
    forall net,
      logs_leaderLogs_nw net ->
      logs_leaderLogs_nw_weak net.
  Proof.
    intros. unfold logs_leaderLogs_nw, logs_leaderLogs_nw_weak in *.
    intros.
    eapply_prop_hyp In In; eauto.
    break_exists_exists; intuition.
  Qed.
    
  Definition logs_leaderLogs_inductive net :=
    logs_leaderLogs net /\
    logs_leaderLogs_nw net.

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
    find_copy_apply_lem_hyp entries_contiguous_invariant.
    find_copy_apply_lem_hyp lift_nextIndex_safety.
    assert (pred (getNextIndex (snd (nwState net h)) h') > 0) by omega.
    unfold nextIndex_safety in *.
    match goal with
      | H : forall _ _, type _ = _ -> _ |- _ => specialize (H h h')
    end. 
    intuition.
    unfold entries_contiguous in *. specialize (H2 h).
    unfold contiguous_range_exact_lo in *. intuition.
    match goal with
      | H : forall _, _ < _ <= _ -> _ |- _ =>
        specialize (H (pred (getNextIndex (snd (nwState net h)) h')))
    end.
    unfold raft_refined_base_params in *.
    repeat find_rewrite_lem deghost_spec. intuition.
    break_exists_exists. intuition.
    apply findAtIndex_intro; eauto using lift_logs_sorted, sorted_uniqueIndices.
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
  

  Ltac prove_in :=
    match goal with
      | [ _ : nwPackets ?net = _,
              _ : In (?p : packet) _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition)
      | [ _ : nwPackets ?net = _,
              _ : pBody ?p = _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; intuition)
    end.

  Ltac update_destruct :=
    match goal with
    | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.
  
  Lemma logs_leaderLogs_inductive_appendEntries :
    refined_raft_net_invariant_append_entries logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros.
    subst. simpl in *. intuition.
    - unfold logs_leaderLogs in *. intros.
      simpl in *. repeat find_higher_order_rewrite.
      update_destruct; subst; rewrite_update; eauto.
      + simpl in *. find_apply_lem_hyp handleAppendEntries_log.
        intuition; repeat find_rewrite; eauto.
        * find_apply_hyp_hyp. break_exists_exists; intuition.
          find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
          simpl in *.
          rewrite update_elections_data_appendEntries_leaderLogs. auto.
        * { subst.
            find_apply_lem_hyp logs_leaderLogs_nw_weaken.
            unfold logs_leaderLogs_nw_weak in *.
            copy_eapply_prop_hyp pBody pBody; eauto.
            break_exists_exists.
            break_exists. intuition.
            - repeat find_higher_order_rewrite.
              update_destruct; subst; rewrite_update; eauto.
              simpl.
              rewrite update_elections_data_appendEntries_leaderLogs.
              auto.
            - repeat find_rewrite. f_equal.
              find_copy_apply_lem_hyp leaderLogs_sorted_invariant; eauto.
              eapply sorted_Prefix_in_eq; eauto.
              intros.
              eapply prefix_contiguous with (i := 0); eauto.
              + admit.
              + eapply leaderLogs_contiguous_invariant; eauto.
              + assert (sorted (log d)) by (eapply entries_sorted_nw_invariant; eauto).
                eapply contiguous_app with (l1 := x1).
                * repeat find_reverse_rewrite.
                  apply removeAfterIndex_sorted. auto.
                * repeat find_reverse_rewrite.
                  eapply removeAfterIndex_contiguous; eauto.
                  eapply entries_contiguous_nw_invariant; eauto.
          }
        * { break_exists. intuition. subst.
            do_in_app. intuition.
            - (* new entry *)
              unfold logs_leaderLogs_nw in *.
              prove_in.
              copy_eapply_prop_hyp In In; eauto.
              match goal with
                | H:exists _, _ |- _ => destruct H as (leader)
              end.
              break_exists; intuition.
              + (* all of the new entries, as well as x, are in the
                new term. This means we can apply the host invariant
                to x and get our leader. *)
                assert (x2 = []).
                {
                  destruct x2; intuition. exfalso.
                  simpl in *. break_match; intuition.
                  simpl in *. subst.
                  find_copy_apply_lem_hyp entries_contiguous_nw_invariant.
                  eapply_prop_hyp entries_contiguous_nw pBody; eauto.
                  unfold contiguous_range_exact_lo in *. intuition.
                  match goal with
                    | _ : removeAfterIndex _ ?index = _ ++ ?e :: _ |- _ =>
                      assert (In e es) by
                          (apply removeAfterIndex_in with (i := index);
                           repeat find_rewrite; intuition)
                  end.
                  eapply_prop_hyp In In. omega.
                } subst. rewrite app_nil_r in *.
                match goal with
                  | H : forall _ _, In _ _ -> _ |- _ =>
                    specialize (H0 (pDst p) x)
                end. intuition.
                break_exists. intuition.
                match goal with
                  | _ : In (_, ?ll) (leaderLogs (_ (_ _ ?h))),
                        _ : removeAfterIndex _ _ = ?es' ++ ?ll |- _ =>
                    exists h, ll, (removeAfterIndex es (eIndex e) ++ es')
                end. intuition.
                * repeat find_rewrite.
                  match goal with
                    | H : forall _, st' _ = _ |- _ =>
                      rewrite H
                  end.
                  update_destruct; subst; rewrite_update; eauto.
                  simpl in *.
                  rewrite update_elections_data_appendEntries_leaderLogs. auto.
                * rewrite removeAfterIndex_in_app; auto.
                  rewrite app_ass. repeat find_rewrite. auto.
                * repeat find_rewrite. do_in_app. intuition; eauto.
              + (* we share an entry with the leader, so we can use
                log matching to make sure our old entries match. we'll
                get the new entries for free from the nw invariant. *)
                break_exists; intuition;
                match goal with
                  | [ _ : In (_, ?ll) (leaderLogs (_ (_ _ ?leader))),
                      _ : removeAfterIndex _ _ = ?es' ++ _ |- _ ] =>
                    exists leader, ll, es'
                end; intuition.
                * repeat find_rewrite.
                  match goal with
                    | H : forall _, st' _ = _ |- _ =>
                      rewrite H
                  end.
                  update_destruct; subst; rewrite_update; eauto.
                  simpl in *.
                  rewrite update_elections_data_appendEntries_leaderLogs. auto.
                * rewrite removeAfterIndex_in_app; auto.
                  repeat find_rewrite. rewrite app_ass.
                  find_copy_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                  f_equal.
                  eapply thing; eauto using lift_logs_sorted;
                  [admit|eapply leaderLogs_entries_match_invariant; eauto|].
                  assert (sorted es) by (eapply entries_sorted_nw_invariant; eauto).
                  find_copy_apply_lem_hyp entries_contiguous_nw_invariant.
                  unfold entries_contiguous_nw in *.
                  copy_eapply_prop_hyp contiguous_range_exact_lo pBody; eauto.
                  find_eapply_lem_hyp removeAfterIndex_contiguous; eauto.
                  match goal with
                    | H : removeAfterIndex _ _ = _ |- _ =>
                      find_erewrite_lem H
                  end.
                  eapply contiguous_app; eauto.
                  repeat find_reverse_rewrite. eauto using removeAfterIndex_sorted.
                * repeat find_rewrite.
                  match goal with
                    | H : forall _, st' _ = _ |- _ =>
                      rewrite H
                  end.
                  update_destruct; subst; rewrite_update; eauto.
                  simpl in *.
                  rewrite update_elections_data_appendEntries_leaderLogs. auto.
                * rewrite removeAfterIndex_in_app; auto.
                  repeat find_rewrite. rewrite app_ass.
                  f_equal.
                  assert (x2 = []).
                  {
                    destruct x2; intuition. exfalso.
                    simpl in *. break_match; intuition.
                    simpl in *. subst.
                    find_copy_apply_lem_hyp entries_contiguous_nw_invariant.
                    eapply_prop_hyp entries_contiguous_nw pBody; eauto.
                    unfold contiguous_range_exact_lo in *. break_and.
                    match goal with
                      | _ : removeAfterIndex _ ?index = _ ++ ?e :: _ |- _ =>
                        assert (In e es) by
                            (apply removeAfterIndex_in with (i := index);
                             repeat find_rewrite; intuition)
                    end.
                    eapply_prop_hyp In In. omega.
                  } subst. simpl.
                  find_copy_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
                  match goal with
                    | |- _ = ?ll =>
                      rewrite removeAfterIndex_maxIndex_sorted with (l := ll) at 2
                  end; eauto.
                  eapply removeAfterIndex_same_sufficient; eauto using lift_logs_sorted;
                  intros;
                  match goal with
                    | _ : eIndex ?e = maxIndex _,
                          _ : In ?e (log _),
                              _ : eIndex ?e' = maxIndex _ |- In ?e'' _ =>
                      assert (eIndex e = eIndex e') as Heq by (repeat find_rewrite; auto);
                        assert (eIndex e'' <= eIndex e) by omega;
                        eapply leaderLogs_entries_match_invariant in Heq; eauto;
                        repeat conclude Heq ltac:(eauto; intuition)
                  end; intuition.
            - (* old entry *)
              (* can use host invariant, since we don't change removeAfterIndex *)
              find_copy_apply_lem_hyp removeAfterIndex_in.
              find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto using lift_logs_sorted.
              find_apply_hyp_hyp. break_exists_exists; intuition.
              + find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
                simpl in *.
                rewrite update_elections_data_appendEntries_leaderLogs. auto.
              + rewrite removeAfterIndex_in_app_l'; eauto;
                [rewrite <- removeAfterIndex_le; auto|].
                intros. eapply gt_le_trans; [|eauto].
                eapply entries_contiguous_nw_invariant; eauto.
          }
      + find_apply_hyp_hyp. break_exists_exists; intuition.
        find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
        simpl in *.
        rewrite update_elections_data_appendEntries_leaderLogs. auto.
    - unfold logs_leaderLogs_nw in *.
      intros. simpl in *. find_apply_hyp_hyp.
      intuition.
      + prove_in.
        copy_eapply_prop_hyp In In; eauto.
        break_exists_exists; intuition;
        repeat find_higher_order_rewrite;
        update_destruct; subst; rewrite_update; eauto;
        simpl in *;
        rewrite update_elections_data_appendEntries_leaderLogs; auto.
      + exfalso. subst. simpl in *.
        unfold handleAppendEntries in *; repeat break_match; find_inversion; congruence.
  Qed.
  
  Lemma logs_leaderLogs_inductive_appendEntriesReply :
    refined_raft_net_invariant_append_entries_reply logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros. intuition.
    - find_apply_lem_hyp handleAppendEntriesReply_log. subst.
      unfold logs_leaderLogs in *. intros.
      simpl in *.
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *;
      repeat find_rewrite;
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
    - find_eapply_lem_hyp handleAppendEntriesReply_packets. subst.
      intuition. unfold logs_leaderLogs_nw in *. intros.
      simpl in *. find_apply_hyp_hyp. intuition.
      prove_in. copy_eapply_prop_hyp In In; eauto.
      break_exists_exists; intuition;
      repeat find_higher_order_rewrite;
      update_destruct; subst; rewrite_update; eauto.
  Qed.


  Lemma logs_leaderLogs_inductive_requestVote :
    refined_raft_net_invariant_request_vote logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros. intuition.
    - find_apply_lem_hyp handleRequestVote_log. subst.
      unfold logs_leaderLogs in *. intros.
      simpl in *.
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *;
      repeat find_rewrite;
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto;
      simpl in *; rewrite update_elections_data_requestVote_leaderLogs; eauto.
    - find_eapply_lem_hyp handleRequestVote_no_append_entries. subst.
      intuition. unfold logs_leaderLogs_nw in *. intros.
      simpl in *. find_apply_hyp_hyp. intuition.
      + prove_in. copy_eapply_prop_hyp In In; eauto.
        break_exists_exists; intuition;
        repeat find_higher_order_rewrite;
        update_destruct; subst; rewrite_update; eauto;
        simpl in *; rewrite update_elections_data_requestVote_leaderLogs; eauto.
      + find_false. subst. simpl in *. subst.
        repeat eexists; eauto.
  Qed.
  
  Lemma logs_leaderLogs_inductive_requestVoteReply :
    refined_raft_net_invariant_request_vote_reply logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros. intuition.
    - subst.
      unfold logs_leaderLogs in *. intros.
      simpl in *.
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *;
      repeat find_rewrite;
      [match goal with
        | H : In _ (log _ ) |- _ =>
          erewrite handleRequestVoteReply_log; eauto;
          erewrite handleRequestVoteReply_log in H; eauto
      end|];
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite ; update_destruct; subst; rewrite_update; eauto;
      simpl in *; apply update_elections_data_requestVoteReply_leaderLogs; eauto.
    - unfold logs_leaderLogs_nw in *. intros.
      simpl in *. find_apply_hyp_hyp. intuition.
      prove_in. copy_eapply_prop_hyp In In; eauto.
      break_exists_exists; intuition;
      repeat find_higher_order_rewrite;
      update_destruct; subst; rewrite_update; eauto;
      simpl in *; apply update_elections_data_requestVoteReply_leaderLogs; eauto.
  Qed.

  Lemma logs_leaderLogs_inductive_clientRequest :
    refined_raft_net_invariant_client_request logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros. intuition.
    - subst.
      unfold logs_leaderLogs in *. intros.
      simpl in *.
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *.
      + find_apply_lem_hyp handleClientRequest_log. intuition; subst; repeat find_rewrite.
        * find_apply_hyp_hyp; break_exists_exists; intuition;
          find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto;
          simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
        * {break_exists. intuition. repeat find_rewrite. simpl in *.
           intuition; subst.
           - find_apply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
             break_exists. intuition.
             unfold ghost_data in *. simpl in *. repeat find_rewrite.
             match goal with
               | h : name, _ : _ = ?e :: ?es ++ ?ll |- _ =>
                 exists h, ll, (e :: x0)
             end; intuition.
             + find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto;
               simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
             + break_if; eauto using app_ass; do_bool; omega.
             + simpl in *. intuition; subst; eauto.
           - find_copy_apply_lem_hyp maxIndex_is_max; eauto using lift_logs_sorted.
             find_apply_hyp_hyp. break_exists_exists; intuition;
             [find_higher_order_rewrite ; update_destruct; subst; rewrite_update; eauto;
              simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto|].
             break_if; do_bool; intuition; omega.
          }
      + find_apply_hyp_hyp; break_exists_exists; intuition;
        find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto;
        simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
    - unfold logs_leaderLogs_nw in *.
      intros. simpl in *. find_apply_hyp_hyp. intuition.
      + eapply_prop_hyp In pBody; eauto; break_exists_exists; intuition; subst;
        repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto;
        simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
      + do_in_map. subst. simpl in *. find_eapply_lem_hyp handleClientRequest_no_append_entries;
          eauto. intuition. find_false. repeat find_rewrite. repeat eexists; eauto.
  Qed.
  
  Lemma logs_leaderLogs_inductive_timeout :
    refined_raft_net_invariant_timeout logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros. intuition.
    - find_apply_lem_hyp handleTimeout_log_same. subst.
      unfold logs_leaderLogs in *. intros.
      simpl in *.
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *;
      repeat find_rewrite;
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto;
      simpl in *; rewrite update_elections_data_timeout_leaderLogs; eauto.
    - intuition. unfold logs_leaderLogs_nw in *. intros.
      simpl in *. find_apply_hyp_hyp. intuition.
      + copy_eapply_prop_hyp In In; eauto.
        break_exists_exists; intuition;
        repeat find_higher_order_rewrite;
        update_destruct; subst; rewrite_update; eauto;
        simpl in *; rewrite update_elections_data_timeout_leaderLogs; eauto.
      + do_in_map. subst. simpl in *.
        find_eapply_lem_hyp handleTimeout_packets; eauto. intuition.
        find_false. repeat find_rewrite.
        repeat eexists; eauto.
  Qed.

  Lemma logs_leaderLogs_inductive_doGenericServer :
    refined_raft_net_invariant_do_generic_server logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    intuition.
    - find_apply_lem_hyp doGenericServer_log.
      unfold logs_leaderLogs in *. intros.
      simpl in *.
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *;
      repeat find_rewrite;
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
    - find_apply_lem_hyp doGenericServer_packets. subst.
      unfold logs_leaderLogs_nw in *. intros. simpl in *.
      find_apply_hyp_hyp. intuition.
      eapply_prop_hyp In In; eauto.
      break_exists_exists; intuition;
      repeat find_higher_order_rewrite;
      update_destruct; subst; rewrite_update; eauto.
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

  Lemma logs_leaderLogs_inductive_doLeader :
    refined_raft_net_invariant_do_leader logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    intuition.
    - unfold logs_leaderLogs in *.
      intros.
      simpl in *.
      find_apply_lem_hyp doLeader_log.
      find_higher_order_rewrite. simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite;
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
    - unfold logs_leaderLogs_nw.
      intros. simpl in *. find_apply_hyp_hyp.
      break_or_hyp.
      + unfold logs_leaderLogs_nw in *.
        eapply_prop_hyp pBody pBody; eauto.
        break_exists_exists; intuition; subst;
        find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
      + { do_in_map. subst. simpl in *.
          find_eapply_lem_hyp doLeader_spec; eauto. intuition.
          - subst. (* just use host invariant *)
            unfold logs_leaderLogs in *.
            find_apply_lem_hyp findGtIndex_necessary.
            intuition.
            eapply_prop_hyp In In.
            break_exists_exists. intuition.
            match goal with
              | _ : In (_, ?ll) _ |- _ =>
                exists ll
            end.
            intuition; eauto using Prefix_refl;
            [find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto|].
            rewrite sorted_findGtIndex_0; eauto using lift_logs_sorted.
            intros. eapply entries_gt_0_invariant; eauto.
          - break_exists. break_and.
            subst.
            unfold logs_leaderLogs in *.
            find_apply_lem_hyp findGtIndex_necessary.
            break_and. find_apply_hyp_hyp.
            match goal with
              | H : exists _ _ _, _ |- _ =>
                destruct H as (leader);
                  destruct H as (ll);
                  destruct H as (es)
            end.
            break_and.
            destruct (lt_eq_lt_dec (maxIndex ll) pli); intuition.
            + exists leader, ll, (findGtIndex es pli), []. intuition.
              * find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
              * simpl; auto.
              * rewrite app_nil_r.
                rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
                unfold ghost_data in *. simpl in *.
                find_rewrite.
                eapply findGtIndex_app_1; omega.
              * eauto using findGtIndex_in.
              * left. intuition.
                match goal with
                  | H : forall _, In _ _ -> _ |- _ =>
                    apply H
                end.
                find_apply_lem_hyp findAtIndex_elim. intuition.
                subst.
                match goal with
                  | _ : In ?x ?l, _ : eIndex ?e > eIndex ?x |- _ =>
                    assert (In x (removeAfterIndex l (eIndex e))) by
                        (apply removeAfterIndex_le_In; eauto; omega)
                end.
                unfold ghost_data in *. simpl in *.
                find_rewrite.
                do_in_app; intuition.
                find_copy_apply_lem_hyp leaderLogs_sorted_invariant; eauto.
                find_apply_lem_hyp maxIndex_is_max; eauto; omega.
            + exists leader, ll, (findGtIndex es pli), []. intuition.
              * find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
              * simpl; auto.
              * rewrite app_nil_r.
                rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
                unfold ghost_data in *. simpl in *.
                find_rewrite.
                apply findGtIndex_app_1. omega.
              * eauto using findGtIndex_in.
              * right. find_apply_lem_hyp findAtIndex_elim.
                left. exists x0. intuition. subst.
                match goal with
                  | _ : In ?x ?l, _ : eIndex ?e > _ |- _ =>
                    assert (In x (removeAfterIndex l (eIndex e))) by
                        (apply removeAfterIndex_le_In; eauto; omega)
                end.
                unfold ghost_data in *. simpl in *.
                find_rewrite.
                assert (sorted (es ++ ll)) by (repeat find_reverse_rewrite;
                                               apply removeAfterIndex_sorted;
                                               repeat find_rewrite; eauto using lift_logs_sorted).
                eapply thing3; eauto; try omega. intros.
                match goal with
                  | |- eIndex ?e > _ =>
                    assert (In e (log (snd (nwState net h)))) by
                        (unfold ghost_data in *; simpl in *;
                         eapply removeAfterIndex_in; repeat find_reverse_rewrite; eauto)
                end. 
                eapply entries_gt_0_invariant; eauto.
            + exists leader, ll, es, (findGtIndex ll pli). intuition.
              * find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
              * (* prefix_findGtIndex *)
                apply findGtIndex_Prefix.
              * rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
                unfold ghost_data in *. simpl in *.
                find_rewrite.
                assert (sorted (es ++ ll)) by (repeat find_reverse_rewrite;
                                               apply removeAfterIndex_sorted;
                                               repeat find_rewrite; eauto using lift_logs_sorted).
                apply findGtIndex_app_2; auto.
              * { right. left.
                  find_apply_lem_hyp findAtIndex_elim. 
                  exists x0.  intuition.
                  - subst.
                    match goal with
                      | H : removeAfterIndex _ _ = _ |- _ =>
                        find_eapply_lem_hyp removeAfterIndex_le_In;
                          [unfold ghost_data in *; simpl in *; find_rewrite_lem H|omega]
                    end.
                    assert (sorted (es ++ ll)) by (repeat find_reverse_rewrite;
                                                   apply removeAfterIndex_sorted;
                                                   repeat find_rewrite; eauto using lift_logs_sorted).
                    eapply thing3; eauto; try omega. intros.
                     match goal with
                       | |- eIndex ?e > _ =>
                         assert (In e (log (snd (nwState net h)))) by
                             (unfold ghost_data in *; simpl in *;
                              eapply removeAfterIndex_in; repeat find_reverse_rewrite; eauto)
                     end. 
                     eapply entries_gt_0_invariant; eauto.
                  - left. intros.
                    eapply findGtIndex_non_empty; eauto.
                }
          - exfalso. (* use nextIndex_sanity *)
            break_exists. intuition.
            find_eapply_lem_hyp nextIndex_sanity; eauto. break_exists.
            unfold ghost_data in *. simpl in *. congruence.
        }
  Qed.

  Lemma logs_leaderLogs_inductive_init :
    refined_raft_net_invariant_init logs_leaderLogs_inductive.
  Proof.
    unfold logs_leaderLogs_inductive. red. intuition.
    - unfold logs_leaderLogs. intros. simpl in *. intuition.
    - unfold logs_leaderLogs_nw. intros. simpl in *. intuition.
  Qed.

  Lemma logs_leaderLogs_inductive_state_same_packets_subset :
    refined_raft_net_invariant_state_same_packet_subset logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intuition.
    - unfold logs_leaderLogs in *. intros.
      repeat find_reverse_higher_order_rewrite.
      find_apply_hyp_hyp. break_exists_exists; intuition.
      find_reverse_higher_order_rewrite. auto.
    - unfold logs_leaderLogs_nw in *. intros.
      find_apply_hyp_hyp. eapply_prop_hyp pBody pBody; eauto.
      break_exists_exists; intuition; subst;
      repeat find_reverse_higher_order_rewrite; auto.
  Qed.

  Lemma logs_leaderLogs_inductive_reboot :
    refined_raft_net_invariant_reboot logs_leaderLogs_inductive.
  Proof.
    red. unfold logs_leaderLogs_inductive. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.
    intuition.
    - subst. unfold logs_leaderLogs in *. intros.
      repeat find_reverse_higher_order_rewrite.
      find_higher_order_rewrite.
      update_destruct; subst; rewrite_update; unfold reboot in *; simpl in *;
      find_apply_hyp_hyp; break_exists_exists; intuition;
      find_higher_order_rewrite; simpl in *; auto;
      update_destruct; subst; rewrite_update; simpl in *; auto.
    - unfold logs_leaderLogs_nw in *. intros.
      find_reverse_rewrite.
      eapply_prop_hyp pBody pBody; eauto.
      break_exists_exists; intuition; subst;
      repeat find_reverse_higher_order_rewrite; auto;
      repeat find_higher_order_rewrite; simpl in *; auto;
      update_destruct; subst; rewrite_update; simpl in *; auto.
  Qed.

  Theorem logs_leaderLogs_inductive_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_leaderLogs_inductive net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply logs_leaderLogs_inductive_init.
    - apply logs_leaderLogs_inductive_clientRequest.
    - apply logs_leaderLogs_inductive_timeout.
    - apply logs_leaderLogs_inductive_appendEntries.
    - apply logs_leaderLogs_inductive_appendEntriesReply.
    - apply logs_leaderLogs_inductive_requestVote.
    - apply logs_leaderLogs_inductive_requestVoteReply.
    - apply logs_leaderLogs_inductive_doLeader.
    - apply logs_leaderLogs_inductive_doGenericServer.
    - apply logs_leaderLogs_inductive_state_same_packets_subset.
    - apply logs_leaderLogs_inductive_reboot.
  Qed.
  
  Theorem logs_leaderLogs_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_leaderLogs net.
  Proof.
    intros. apply logs_leaderLogs_inductive_invariant. auto.
  Qed.

  Theorem logs_leaderLogs_nw_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      logs_leaderLogs_nw net.
  Proof.
    intros. apply logs_leaderLogs_inductive_invariant. auto.
  Qed.

  Instance llli : logs_leaderLogs_interface.
  Proof.
    split; eauto using logs_leaderLogs_invariant, logs_leaderLogs_nw_invariant.
  Qed.

End LogsLeaderLogs.
