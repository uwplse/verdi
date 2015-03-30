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
  Context {nisi : nextIndex_safety_interface}.
  Context {si : sorted_interface}.

  Definition logs_leaderLogs_nw net :=
    forall p t n pli plt es ci e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e es ->
      exists leader ll es' ll',
        In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\
        Prefix ll' ll /\
        removeAfterIndex es (eIndex e) = es' ++ ll' /\
        (forall e', In e' es' -> eTerm e' = eTerm e) /\
        ((plt = eTerm e /\ pli > maxIndex ll)  \/
         (exists e, In e ll /\ eIndex e = pli /\ eTerm e = plt /\ (ll' <> [] \/
                                                             pli = maxIndex ll)) \/
         plt = 0 /\ pli = 0).


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
  
  Require Import Omega.

  Lemma sorted_Prefix_in_eq :
    forall l' l,
      sorted l ->
      Prefix l' l ->
      (forall e, In e l -> In e l') ->
      l' = l.
  Proof.
    induction l'; intros; simpl in *; intuition.
    - destruct l; simpl in *; auto.
      specialize (H1 e); intuition.
    - break_match; intuition. subst.
      simpl in *. intuition. f_equal.
      eapply IHl'; eauto.
      intros.
      specialize (H1 e0); intuition.
      subst. specialize (H0 e0); intuition. omega.
  Qed.

  Lemma removeAfterIndex_eq :
    forall l i,
      (forall e, In e l -> eIndex e <= i) ->
      removeAfterIndex l i = l.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; intuition.
    do_bool. specialize (H a). intuition. omega.
  Qed.

    
  Lemma removeAfterIndex_in_app :
    forall l l' e,
      In e l ->
      removeAfterIndex (l ++ l') (eIndex e) =
      (removeAfterIndex l (eIndex e)) ++ l'.
  Proof.
    induction l; intros; simpl in *; intuition;
    subst; break_if; do_bool; eauto using app_ass.
    omega.
  Qed.

  Lemma removeAfterIndex_in_app_l' :
    forall l l' e,
      (forall e', In e' l -> eIndex e' > eIndex e) ->
      In e l' ->
      removeAfterIndex (l ++ l') (eIndex e) =
      removeAfterIndex l' (eIndex e).
  Proof.
    induction l; intros; simpl in *; intuition;
    subst; break_if; do_bool; eauto using app_ass.
    specialize (H a). intuition. omega.
  Qed.

  Lemma removeAfterIndex_maxIndex_sorted :
    forall l,
      sorted l ->
      l = removeAfterIndex l (maxIndex l).
  Proof.
    intros; induction l; simpl in *; intuition.
    break_if; auto. do_bool. omega.
  Qed.

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
                  [eapply leaderLogs_entries_match_invariant; eauto|].
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
    admit.
  Qed.


  Lemma logs_leaderLogs_inductive_requestVote :
    refined_raft_net_invariant_request_vote logs_leaderLogs_inductive.
  Proof.
    admit.
  Qed.
  
  Lemma logs_leaderLogs_inductive_requestVoteReply :
    refined_raft_net_invariant_request_vote_reply logs_leaderLogs_inductive.
  Proof.
    admit.
  Qed.

  Lemma logs_leaderLogs_inductive_clientRequest :
    refined_raft_net_invariant_client_request logs_leaderLogs_inductive.
  Proof.
    admit.
  Qed.
  
  Lemma logs_leaderLogs_inductive_timeout :
    refined_raft_net_invariant_timeout logs_leaderLogs_inductive.
  Proof.
    admit.
  Qed.

  Lemma logs_leaderLogs_inductive_doGenericServer :
    refined_raft_net_invariant_do_generic_server logs_leaderLogs_inductive.
  Proof.
    admit.
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
      find_rewrite. eauto.
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
    - admit.
    - unfold logs_leaderLogs_nw.
      intros. simpl in *. find_apply_hyp_hyp.
      break_or_hyp.
      + admit.
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
                Lemma findGtIndex_nil :
                  forall l i,
                    (forall e', In e' l -> eIndex e' <= i) ->
                    findGtIndex l i = [].
                Proof.
                  intros; induction l; simpl in *; intuition.
                  break_if; do_bool; intuition.
                  specialize (H a); intuition. omega.
                Qed.
                Lemma findGtIndex_removeAfterIndex_commute :
                  forall l i i',
                    sorted l ->
                    removeAfterIndex (findGtIndex l i) i' =
                    findGtIndex (removeAfterIndex l i') i.
                Proof.
                  intros. induction l; simpl in *; auto.
                  repeat (break_if; simpl; intuition); do_bool;
                  try congruence.
                  symmetry. apply findGtIndex_nil.
                  intros. find_apply_lem_hyp removeAfterIndex_in.
                  find_apply_hyp_hyp. intuition.
                Qed.
                rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
                unfold ghost_data in *. simpl in *.
                find_rewrite.

                Lemma findGtIndex_app_1 :
                  forall l l' i,
                    maxIndex l' <= i ->
                    findGtIndex (l ++ l') i = findGtIndex l i.
                Proof.
                  induction l; intros; simpl in *; intuition.
                  - destruct l'; simpl in *; intuition.
                    break_if; do_bool; auto; omega.
                  - break_if; do_bool; auto.
                    f_equal. eauto.
                Qed.
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
                Lemma thing3 :
                  forall l l' e,
                    sorted (l ++ l') ->
                    (forall e', In e' (l ++ l') -> eIndex e' > 0) ->
                    In e (l ++ l') ->
                    eIndex e <= maxIndex l' ->
                    In e l'.
                Proof.
                  induction l; intros; simpl in *; intuition.
                  subst. destruct l'; simpl in *; intuition.
                  - exfalso. specialize (H0 e). intuition.
                  - exfalso. specialize (H3 e0). conclude_using intuition.
                    intuition.
                Qed.
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
                Lemma findGtIndex_app_2 :
                  forall l l' i,
                    sorted (l ++ l') ->
                    i < maxIndex l' ->
                    findGtIndex (l ++ l') i = l ++ findGtIndex l' i.
                Proof.
                  induction l; intros; simpl in *; intuition.
                  break_if; do_bool; auto.
                  - f_equal. eauto.
                  - exfalso.
                    destruct l'; simpl in *; intuition.
                    specialize (H1 e); conclude_using intuition; intuition.
                Qed.
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
                    Lemma findGtIndex_non_empty :
                      forall l i,
                        i < maxIndex l ->
                        findGtIndex l i <> [].
                    Proof.
                      intros. induction l; simpl in *; intuition.
                      break_if; do_bool; simpl in *; intuition.
                      congruence.
                    Qed.
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
    admit.
  Qed.

  Lemma logs_leaderLogs_inductive_state_same_packets_subset :
    refined_raft_net_invariant_state_same_packet_subset logs_leaderLogs_inductive.
  Proof.
    admit.
  Qed.

  Lemma logs_leaderLogs_inductive_reboot :
    refined_raft_net_invariant_reboot logs_leaderLogs_inductive.
  Proof.
    admit.
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

  Instance llli : logs_leaderLogs_interface.
  Proof.
    split. eauto using logs_leaderLogs_invariant.
  Qed.

End LogsLeaderLogs.
