Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import RaftState.
Require Import Raft.
Require Import CommonTheorems.
Require Import CommitRecordedCommittedInterface.
Require Import StateMachineSafetyInterface.
Require Import StateMachineSafetyPrimeInterface.
Require Import RaftRefinementInterface.
Require Import MaxIndexSanityInterface.
Require Import LeaderCompletenessInterface.
Require Import SortedInterface.
Require Import LogMatchingInterface.
Require Import PrevLogLeaderSublogInterface.
Require Import CurrentTermGtZeroInterface.
Require Import LastAppliedLeCommitIndexInterface.
Require Import MatchIndexAllEntriesInterface.
Require Import LeadersHaveLeaderLogsInterface.
Require Import LeaderSublogInterface.
Require Import TermsAndIndicesFromOneLogInterface.
Require Import GhostLogCorrectInterface.
Require Import GhostLogsLogPropertiesInterface.
Require Import GhostLogLogMatchingInterface.
Require Import TransitiveCommitInterface.
Require Import TermSanityInterface.

Require Import RefinedLogMatchingLemmasInterface.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import RaftMsgRefinementInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section StateMachineSafetyProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {si : sorted_interface}.
  Context {lmi : log_matching_interface}.
  Context {smspi : state_machine_safety'interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {pllsi : prevLog_leader_sublog_interface}.
  Context {ctgt0 : current_term_gt_zero_interface}.
  Context {lalcii : lastApplied_le_commitIndex_interface}.
  Context {miaei : match_index_all_entries_interface}.
  Context {lhlli : leaders_have_leaderLogs_interface}.
  Context {lci : leader_completeness_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {taifoli : terms_and_indices_from_one_log_interface}.
  Context {glci : ghost_log_correct_interface}.
  Context {lphogli : log_properties_hold_on_ghost_logs_interface}.
  Context {glemi : ghost_log_entries_match_interface}.
  Context {tci : transitive_commit_interface}.
  Context {tsi : term_sanity_interface}.
  
  Context {rmri : raft_msg_refinement_interface}.

  Lemma exists_deghost_packet :
    forall net p,
      In p (nwPackets (deghost net)) ->
      exists (q : packet (params := raft_refined_multi_params)),
        In q (nwPackets net) /\ p = deghost_packet q.
  Proof.
    intros.
    unfold deghost in *. simpl in *. do_in_map.
    subst. eexists; eauto.
  Qed.

  Lemma state_machine_safety_deghost :
    forall net,
      commit_recorded_committed net ->
      state_machine_safety' net ->
      state_machine_safety (deghost net).
  Proof.
    intros. unfold state_machine_safety in *. intuition.
    - unfold state_machine_safety_host. intros.
      do 2 eapply_prop_hyp commit_recorded_committed commit_recorded.
      unfold state_machine_safety' in *. intuition. eauto.
    - unfold state_machine_safety_nw. intros.
      eapply_prop_hyp commit_recorded_committed commit_recorded.
      unfold state_machine_safety', state_machine_safety_nw' in *. intuition.
      find_apply_lem_hyp exists_deghost_packet. break_exists.
      intuition. subst. simpl in *. repeat break_match. simpl in *.
      subst. eapply_prop_hyp In In; repeat find_rewrite; simpl; eauto.
  Qed.

  Definition ghost_log_network : Type := @network _ raft_msg_refined_multi_params.
  Definition ghost_log_packet : Type := @packet _ raft_msg_refined_multi_params.

  Definition lifted_maxIndex_sanity (net : ghost_log_network) : Prop :=
    (forall h,
      lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))) /\
    (forall h, commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))).

  Lemma lifted_maxIndex_sanity_init :
    msg_refined_raft_net_invariant_init lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_init, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
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

  Lemma lifted_sorted_host :
    forall net h,
      refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    find_insterU. conclude_using eauto.
    unfold logs_sorted, logs_sorted_host in *. break_and.
    unfold deghost in *. simpl in *. break_match. eauto.
  Qed.

  Lemma msg_lifted_sorted_host :
    forall net h,
      msg_refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    rewrite <- msg_deghost_spec with (net0 := net).
    eapply msg_lift_prop.
    - auto using lifted_sorted_host.
    - auto.
  Qed.
  
  Lemma lifted_sorted_network :
    forall net p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      sorted es.
  Proof.
    intros. eapply entries_sorted_nw_invariant; eauto.
  Qed.

  Definition lifted_no_entries_past_current_term_host net :=
    forall (h : name) e,
      In e (log (snd (nwState net h))) ->
      eTerm e <= currentTerm (snd (nwState net h)).

  Lemma lifted_no_entries_past_current_term_host_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_no_entries_past_current_term_host net.
  Proof.
    intros.
    enough (no_entries_past_current_term_host (deghost (mgv_deghost net))) by
        (unfold no_entries_past_current_term_host, lifted_no_entries_past_current_term_host, deghost, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop_all_the_way; eauto.
    intros.
    eapply no_entries_past_current_term_invariant; eauto.
  Qed.

  Lemma all_the_way_deghost_spec :
    forall (net : ghost_log_network) h,
      snd (nwState net h) = nwState (deghost (mgv_deghost net)) h.
  Proof.
    intros.
    rewrite deghost_spec.
    rewrite msg_deghost_spec with (net0 := net).
    auto.
  Qed.

  Lemma all_the_way_simulation_1 :
    forall (net : ghost_log_network),
      msg_refined_raft_intermediate_reachable net ->
      raft_intermediate_reachable (deghost (mgv_deghost net)).
  Proof.
    auto using simulation_1, msg_simulation_1.
  Qed.

  Lemma lifted_maxIndex_sanity_client_request :
    msg_refined_raft_net_invariant_client_request lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_client_request, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    simpl. intros.
    find_copy_apply_lem_hyp handleClientRequest_maxIndex.
    - intuition; simpl in *; repeat find_higher_order_rewrite; update_destruct; auto.
      + erewrite handleClientRequest_lastApplied by eauto. eauto using le_trans.
      + erewrite handleClientRequest_commitIndex by eauto. eauto using le_trans.
    - match goal with H : _ |- _ => rewrite all_the_way_deghost_spec with (net := net) in H end.
        eapply handleClientRequest_logs_sorted; eauto.
        * auto using all_the_way_simulation_1.
        * apply logs_sorted_invariant. auto using all_the_way_simulation_1.
  Qed.

  Lemma lifted_maxIndex_sanity_timeout :
    msg_refined_raft_net_invariant_timeout lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_timeout, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; simpl in *; repeat find_higher_order_rewrite; update_destruct; auto;
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

  Lemma in_ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof.
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma in_mgv_ghost_packet :
    forall (net : ghost_log_network) p,
      In p (nwPackets net) ->
      In (mgv_deghost_packet p) (nwPackets (mgv_deghost net)).
  Proof.
    unfold mgv_deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma pBody_deghost_packet :
    forall (p : packet (params := raft_refined_multi_params)),
      pBody (deghost_packet p) = pBody p.
  Proof.
    unfold deghost_packet.
    simpl. auto.
  Qed.

  Lemma pDst_deghost_packet :
    forall (p : packet (params := raft_refined_multi_params)),
      pDst (deghost_packet p) = pDst p.
  Proof.
    unfold deghost_packet.
    simpl. auto.
  Qed.

  Lemma pDst_mgv_deghost_packet :
    forall (p : ghost_log_packet),
      pDst (mgv_deghost_packet p) = pDst p.
  Proof.
    unfold mgv_deghost_packet.
    simpl. auto.
  Qed.

  Lemma pBody_mgv_deghost_packet :
    forall (p : ghost_log_packet),
      pBody (mgv_deghost_packet p) = snd (pBody p).
  Proof.
    unfold mgv_deghost_packet.
    simpl. auto.
  Qed.

  Lemma lifted_handleAppendEntries_logs_sorted :
    forall (net : ghost_log_network) (p : ghost_log_packet) t n pli plt es ci st' m,
      msg_refined_raft_intermediate_reachable net ->
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (st', m) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      In p (nwPackets net) ->
      sorted (log st').
  Proof.
    intros.
    eapply handleAppendEntries_logs_sorted with (p0 := deghost_packet (mgv_deghost_packet p)).
    - eauto using all_the_way_simulation_1.
    - apply lift_prop.
      + apply logs_sorted_invariant.
      + auto using msg_simulation_1.
    - rewrite <- all_the_way_deghost_spec.
      rewrite pDst_deghost_packet.
      rewrite pDst_mgv_deghost_packet.
      eauto.
    - rewrite pBody_deghost_packet.
      rewrite pBody_mgv_deghost_packet.
      auto.
    - apply in_ghost_packet. apply in_mgv_ghost_packet. auto.
  Qed.

  Lemma contiguous_range_exact_lo_elim_exists :
    forall es lo i,
      contiguous_range_exact_lo es lo ->
      lo < i <= maxIndex es -> exists e, eIndex e = i /\ In e es.
  Proof.
    unfold contiguous_range_exact_lo.
    intuition.
  Qed.

  Lemma contiguous_range_exact_lo_elim_lt :
    forall es lo e,
      contiguous_range_exact_lo es lo ->
      In e es ->
      lo < eIndex e.
  Proof.
    unfold contiguous_range_exact_lo.
    intuition.
  Qed.

  Lemma lifted_sms_nw :
    forall (net : network (params := raft_refined_multi_params)) h p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
      state_machine_safety (deghost net) ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      t >= currentTerm (snd (nwState net h)) ->
      commit_recorded (deghost net) h e ->
      (prevLogIndex > eIndex e \/
       (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/
       eIndex e > maxIndex entries \/
       In e entries).
  Proof.
    unfold state_machine_safety, state_machine_safety_nw.
    intuition.
    match goal with
      | [ H : _ |- _ ] => eapply H with (p := deghost_packet p)
    end.
    - auto using in_ghost_packet.
    - rewrite pBody_deghost_packet. eauto.
    - rewrite deghost_spec. eauto.
    - auto.
  Qed.


  Lemma msg_lifted_sms_nw :
    forall (net : ghost_log_network) h p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
      state_machine_safety (deghost (mgv_deghost net)) ->
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm
                                    entries leaderCommit ->
      t >= currentTerm (snd (nwState net h)) ->
      commit_recorded (deghost (mgv_deghost net)) h e ->
      (prevLogIndex > eIndex e \/
       (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/
       eIndex e > maxIndex entries \/
       In e entries).
  Proof.
    intros.
    eapply lifted_sms_nw.
    - eauto.
    - eauto using in_mgv_ghost_packet.
    - rewrite pBody_mgv_deghost_packet. eauto.
    - rewrite msg_deghost_spec with (net0 := net). eauto.
    - auto.
  Qed.

  Lemma commit_recorded_lift_intro :
    forall (net : network (params := raft_refined_multi_params)) h e,
      In e (log (snd (nwState net h))) ->
      (eIndex e <= lastApplied (snd (nwState net h)) \/
       eIndex e <= commitIndex (snd (nwState net h))) ->
      commit_recorded (deghost net) h e.
  Proof.
    unfold commit_recorded.
    intros.
    rewrite deghost_spec.
    auto.
  Qed.

  Lemma msg_commit_recorded_lift_intro :
    forall (net : ghost_log_network) h e,
      In e (log (snd (nwState net h))) ->
      (eIndex e <= lastApplied (snd (nwState net h)) \/
       eIndex e <= commitIndex (snd (nwState net h))) ->
      commit_recorded (deghost (mgv_deghost net)) h e.
  Proof.
    unfold commit_recorded.
    intros.
    rewrite deghost_spec.
    rewrite msg_deghost_spec with (net0 := net).
    auto.
  Qed.

  Definition lifted_entries_contiguous (net : ghost_log_network) : Prop :=
    forall h, contiguous_range_exact_lo (log (snd (nwState net h))) 0.

  Lemma lifted_entries_contiguous_invariant :
    forall net, msg_refined_raft_intermediate_reachable net ->
           lifted_entries_contiguous net.
  Proof.
    unfold lifted_entries_contiguous.
    intros.
    pose proof (msg_lift_prop _ entries_contiguous_invariant _ $(eauto)$ h).
    find_rewrite_lem msg_deghost_spec.
    auto.
  Qed.

  Definition lifted_entries_contiguous_nw (net : ghost_log_network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      contiguous_range_exact_lo es pli.

  Lemma lifted_entries_contiguous_nw_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_contiguous_nw net.
  Proof.
    unfold lifted_entries_contiguous_nw.
    intros.
    pose proof msg_lift_prop _ entries_contiguous_nw_invariant _ $(eauto)$ (mgv_deghost_packet p).
    match goal with
    | [ H : context [In] |- _ ] => eapply H
    end.
    - auto using in_mgv_ghost_packet.
    - rewrite pBody_mgv_deghost_packet. eauto.
  Qed.

  Definition lifted_entries_gt_0 (net : ghost_log_network) : Prop :=
    forall h e,
      In e (log (snd (nwState net h))) -> eIndex e > 0.

  Lemma lifted_entries_gt_0_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_gt_0 net.
  Proof.
    unfold lifted_entries_gt_0.
    intros.
    pose proof msg_lift_prop _ entries_gt_0_invariant _ $(eauto)$.
    unfold entries_gt_0 in *.
    match goal with
    | [ H : _ |- _ ] => eapply H; eauto
    end.
    rewrite msg_deghost_spec.
    eauto.
  Qed.

  Lemma lifted_maxIndex_sanity_append_entries :
    forall xs (p : ghost_log_packet) ys (net : ghost_log_network) st' ps' gd d m t n pli plt es ci,
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) ->
      gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      lifted_maxIndex_sanity net ->
      state_machine_safety (deghost (mgv_deghost net)) ->
      msg_refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall (p' : ghost_log_packet), In p' ps' -> In p' (xs ++ ys) \/
                         mgv_deghost_packet p' = mkPacket (params := raft_refined_multi_params)
                                                          (pDst p) (pSrc p) m) ->
      lifted_maxIndex_sanity (mkNetwork ps' st').
  Proof.
    unfold lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intros.
    intuition; simpl in *; repeat find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleAppendEntries_lastApplied by eauto.
      assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
      match goal with
        | _ : handleAppendEntries ?h ?s ?t ?n ?pli ?plt ?es ?ci = (?s', ?m) |- _ =>
          pose proof handleAppendEntries_log_detailed
               h s t n pli plt es ci s' m
      end.
      intuition; repeat find_rewrite.
      + eauto.
      + subst.
        destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p))))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        assert (exists x, eIndex x = maxIndex (log d) /\ In x (log (snd (nwState net (pDst p))))).
        {
          eapply contiguous_range_exact_lo_elim_exists.
          - eapply lifted_entries_contiguous_invariant. auto.
          - split.
            + find_apply_lem_hyp maxIndex_non_empty. break_exists.  break_and.
              repeat find_rewrite.
              eapply contiguous_range_exact_lo_elim_lt.
              * eapply lifted_entries_contiguous_nw_invariant; eauto.
              * auto.
            + eapply le_trans; [|eauto]. simpl in *. omega.
        }
        break_exists. break_and.
        eapply findAtIndex_None; [|eauto| |]; eauto.
        apply msg_lifted_sorted_host; auto.
      + subst.
        destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p))))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.

        find_eapply_lem_hyp msg_lifted_sms_nw; eauto;
        [|eapply msg_commit_recorded_lift_intro; eauto;
        left; repeat find_rewrite; auto using lt_le_weak].
        intuition.
        * subst.
          assert (0 < eIndex x) by (eapply lifted_entries_contiguous_invariant; eauto).
          omega.
        * destruct (log d); intuition. simpl in *.
          intuition; subst; auto.
          find_apply_hyp_hyp. omega.
      + destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) pli); intuition;
        [eapply le_trans; [| apply sorted_maxIndex_app]; auto;
         break_exists; break_and;
         erewrite maxIndex_removeAfterIndex by (eauto; apply msg_lifted_sorted_host; auto);
         auto|]; [idtac].

        destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; simpl in *; intuition|]; [idtac].
        assert (exists x, eIndex x = maxIndex es /\ In x (log (snd (nwState net (pDst p))))).
        {
          eapply contiguous_range_exact_lo_elim_exists.
          - eapply lifted_entries_contiguous_invariant. auto.
          - split.
            + find_apply_lem_hyp maxIndex_non_empty. break_exists.  break_and.
              repeat find_rewrite.
              destruct es.
              * simpl in *. intuition.
              * simpl.  subst.
                { eapply le_lt_trans with (m := eIndex x).
                  - omega.
                  - eapply contiguous_range_exact_lo_elim_lt.
                    + eapply lifted_entries_contiguous_nw_invariant; eauto.
                    + intuition.
                }
            + eapply le_trans; [|eauto]. simpl in *. omega.
        }
        break_exists. intuition.
        match goal with
          | H : findAtIndex _ _ = None |- _ =>
            eapply findAtIndex_None with (x1 := x) in H
        end; eauto.
        * congruence.
        * apply msg_lifted_sorted_host. auto.
      +   destruct (le_lt_dec (lastApplied (snd (nwState net (pDst p)))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; simpl in *; intuition|]; [idtac].
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.
        find_copy_apply_lem_hyp maxIndex_non_empty.
        break_exists. intuition.

        find_eapply_lem_hyp msg_lifted_sms_nw; eauto;
        [|eapply msg_commit_recorded_lift_intro; eauto;
        left; repeat find_rewrite; auto using lt_le_weak].

        match goal with
          | _ : In ?x es, _ : maxIndex es = eIndex ?x |- _ =>
            assert (pli < eIndex x)
                   by ( eapply contiguous_range_exact_lo_elim_lt; eauto;
                        eapply lifted_entries_contiguous_nw_invariant; eauto)
        end.
        intuition.

        match goal with
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
    - assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
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
        destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p))))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        assert (exists x, eIndex x = maxIndex (log d) /\ In x (log (snd (nwState net (pDst p))))).
        {
          eapply contiguous_range_exact_lo_elim_exists.
          - eapply lifted_entries_contiguous_invariant. auto.
          - split.
            + find_apply_lem_hyp maxIndex_non_empty. break_exists.  break_and.
              repeat find_rewrite.
              eapply contiguous_range_exact_lo_elim_lt.
              * eapply lifted_entries_contiguous_nw_invariant; eauto.
              * auto.
            + eapply le_trans; [|eauto]. simpl in *. omega.
        }
        break_exists. intuition.
        find_eapply_lem_hyp findAtIndex_None; eauto.
        apply msg_lifted_sorted_host. auto.
      + subst.
        destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p))))
                            (maxIndex (log d))); auto.
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.

        find_eapply_lem_hyp msg_lifted_sms_nw; eauto;
        [|eapply msg_commit_recorded_lift_intro; eauto;
        right; repeat find_rewrite; intuition].
        intuition.
        * subst.
          assert (0 < eIndex x) by (eapply lifted_entries_contiguous_invariant; eauto).
          omega.
        * destruct (log d); intuition. simpl in *.
          intuition; subst; auto.
          find_apply_hyp_hyp. omega.
      + destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) pli); intuition;
        [eapply le_trans; [| apply sorted_maxIndex_app]; auto;
         break_exists; intuition;
         erewrite maxIndex_removeAfterIndex; eauto; apply msg_lifted_sorted_host; auto|]; [idtac].
        destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; simpl in *; intuition|]; [idtac].
        assert (exists x, eIndex x = maxIndex es /\ In x (log (snd (nwState net (pDst p))))).
        {
          eapply contiguous_range_exact_lo_elim_exists.
          - eapply lifted_entries_contiguous_invariant. auto.
          - split.
            + find_apply_lem_hyp maxIndex_non_empty. break_exists.  break_and.
              repeat find_rewrite.
              destruct es.
              * simpl in *. intuition.
              * simpl.  subst.
                { eapply le_lt_trans with (m := eIndex x).
                  - omega.
                  - eapply contiguous_range_exact_lo_elim_lt.
                    + eapply lifted_entries_contiguous_nw_invariant; eauto.
                    + intuition.
                }
            + eapply le_trans; [|eauto]. simpl in *. omega.
        }
        break_exists. intuition.
        match goal with
          | H : findAtIndex _ _ = None |- _ =>
            eapply findAtIndex_None with (x1 := x) in H
        end; eauto.
        * congruence.
        * apply msg_lifted_sorted_host; auto.
      + destruct (le_lt_dec (commitIndex (snd (nwState net (pDst p)))) (maxIndex es)); intuition;
        [match goal with
           | |- context [ maxIndex (?ll1 ++ ?ll2) ] =>
             pose proof maxIndex_app ll1 ll2
         end; simpl in *; intuition|]; [idtac].
        exfalso.
        assert (In p (nwPackets net)) by (find_rewrite; intuition).
        break_exists; intuition. find_apply_lem_hyp findAtIndex_elim; intuition.
        find_copy_apply_lem_hyp maxIndex_non_empty.
        break_exists. intuition.

        find_eapply_lem_hyp msg_lifted_sms_nw; eauto;
        [|eapply msg_commit_recorded_lift_intro; eauto;
        right; repeat find_rewrite; intuition].
        match goal with
          | _ : In ?x es, _ : maxIndex es = eIndex ?x |- _ =>
            assert (pli < eIndex x)
              by (eapply contiguous_range_exact_lo_elim_lt; eauto;
                        eapply lifted_entries_contiguous_nw_invariant; eauto)
        end.

        intuition.
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

  Lemma lifted_maxIndex_sanity_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_append_entries_reply,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; repeat find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleAppendEntriesReply_same_lastApplied by eauto.
      erewrite handleAppendEntriesReply_same_log by eauto.
      auto.
    - erewrite handleAppendEntriesReply_same_commitIndex by eauto.
      erewrite handleAppendEntriesReply_same_log by eauto.
      auto.
  Qed.

  Lemma lifted_maxIndex_sanity_request_vote :
    msg_refined_raft_net_invariant_request_vote lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_request_vote,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; repeat find_higher_order_rewrite; update_destruct; auto.
    - erewrite handleRequestVote_same_log by eauto.
      erewrite handleRequestVote_same_lastApplied by eauto.
      auto.
    - erewrite handleRequestVote_same_log by eauto.
      erewrite handleRequestVote_same_commitIndex by eauto.
      auto.
  Qed.

  Lemma lifted_maxIndex_sanity_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_request_vote_reply,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; repeat find_higher_order_rewrite; update_destruct; auto.
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

  Lemma lifted_maxIndex_sanity_do_leader :
    msg_refined_raft_net_invariant_do_leader lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_do_leader,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; repeat find_higher_order_rewrite; update_destruct; auto.
    - erewrite doLeader_same_log by eauto.
      erewrite doLeader_same_lastApplied by eauto.
      repeat match goal with
        | [ H : forall _ , _ |- _ ] => specialize (H h0)
      end.
      unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
      simpl in *.
      repeat find_rewrite. auto.
    - repeat match goal with
                 | [ H : forall _ , _ |- _ ] => specialize (H h0)
               end.
      unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
      simpl in *.
      repeat find_rewrite. simpl in *.
      erewrite doLeader_same_commitIndex; eauto.
      find_eapply_lem_hyp (msg_lifted_sorted_host net h0).
      unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
      simpl in *.
      find_rewrite. auto.
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


  Lemma lifted_maxIndex_sanity_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_do_generic_server,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_higher_order_rewrite; update_destruct; auto;
    erewrite doGenericServer_log by eauto.
    - repeat match goal with
               | [ H : forall _ , _ |- _ ] => specialize (H h0)
             end.
      repeat find_rewrite. simpl in *.
      find_apply_lem_hyp doGenericServer_lastApplied.
      unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
      simpl in *.
      intuition; repeat find_rewrite; auto.
    - repeat match goal with
               | [ H : forall _ , _ |- _ ] => specialize (H h0)
             end.
      unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
      simpl in *.
      repeat find_rewrite. simpl in *.
      erewrite doGenericServer_commitIndex by eauto.
      auto.
  Qed.

  Lemma lifted_maxIndex_sanity_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_state_same_packet_subset,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; find_reverse_higher_order_rewrite; auto.
  Qed.

  Lemma lifted_maxIndex_sanity_reboot :
    msg_refined_raft_net_invariant_reboot lifted_maxIndex_sanity.
  Proof.
    unfold msg_refined_raft_net_invariant_reboot,
           lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    unfold reboot.
    intuition; find_higher_order_rewrite; update_destruct; auto with *;
    repeat match goal with
             | [ H : forall _ , _ |- _ ] => specialize (H h0)
           end;
    unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *;
    simpl in *;
    repeat find_rewrite; simpl in *;
    auto.
  Qed.

  Definition lifted_directly_committed (net : ghost_log_network) (e : entry) : Prop :=
    exists quorum,
      NoDup quorum /\
      length quorum > div2 (length nodes) /\
      (forall h, In h quorum -> In (eTerm e, e) (allEntries (fst (nwState net h)))).

  Definition lifted_committed (net : ghost_log_network) (e : entry) (t : term) : Prop :=
    exists h e',
      eTerm e' <= t /\
      lifted_directly_committed net e' /\
      eIndex e <= eIndex e' /\
      In e (log (snd (nwState net h))) /\ In e' (log (snd (nwState net h))).

  Definition commit_invariant_host (net : ghost_log_network) : Prop :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      eIndex e <= commitIndex (snd (nwState net h)) ->
      lifted_committed net e (currentTerm (snd (nwState net h))).

  Definition commit_invariant_nw (net : ghost_log_network) : Prop :=
    forall p t lid pli plt es lci e,
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t lid pli plt es lci ->
      In e (fst (pBody p)) ->
      eIndex e <= lci ->
      lifted_committed net e t.

  Definition commit_invariant (net : ghost_log_network) : Prop :=
    commit_invariant_host net /\
    commit_invariant_nw net.

  Lemma commit_invariant_init :
    msg_refined_raft_net_invariant_init commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_init, commit_invariant.
    split.
    - unfold commit_invariant_host, commit_recorded_committed, commit_recorded, committed. simpl.
      intuition.
    - unfold commit_invariant_nw; simpl; intuition.
  Qed.

  Lemma msg_lifted_lastApplied_le_commitIndex :
    forall net h,
      msg_refined_raft_intermediate_reachable net ->
      lastApplied (snd (nwState net h)) <= commitIndex (snd (nwState net h)).
  Proof.
    intros.
    pose proof (lift_prop _ (lastApplied_le_commitIndex_invariant)).
    find_apply_lem_hyp msg_simulation_1.
    find_apply_hyp_hyp.
    unfold lastApplied_le_commitIndex in *.
    match goal with
    | [ H : _ |- _ ] => specialize (H h)
    end.
    find_rewrite_lem deghost_spec.
    find_rewrite_lem msg_deghost_spec.
    auto.
  Qed.

  Lemma lifted_directly_committed_directly_committed :
    forall net e,
      lifted_directly_committed net e ->
      directly_committed (mgv_deghost net) e.
  Proof.
    unfold lifted_directly_committed, directly_committed.
    intuition.
    break_exists_exists.
    intuition.
    rewrite msg_deghost_spec. auto.
  Qed.

  Lemma directly_committed_lifted_directly_committed :
    forall net e,
      directly_committed (mgv_deghost net) e ->
      lifted_directly_committed net e.
  Proof.
    unfold lifted_directly_committed, directly_committed.
    intuition.
    break_exists_exists.
    intuition.
    find_apply_hyp_hyp.
    find_rewrite_lem msg_deghost_spec. auto.
  Qed.

  Lemma lifted_committed_committed :
    forall net e t,
      lifted_committed net e t ->
      committed (mgv_deghost net) e t.
  Proof.
    unfold lifted_committed, committed.
    intros.
    break_exists_exists.
    rewrite msg_deghost_spec.
    intuition auto using lifted_directly_committed_directly_committed.
  Qed.

  Lemma committed_lifted_committed :
    forall net e t,
      committed (mgv_deghost net) e t ->
      lifted_committed net e t.
  Proof.
    unfold lifted_committed, committed.
    intros.
    break_exists_exists.
    find_rewrite_lem msg_deghost_spec.
    intuition auto using directly_committed_lifted_directly_committed.
  Qed.

  Lemma msg_deghost_spec' :
    forall base multi failure ghost
      (net : @network (@mgv_refined_base_params base)
                      (@mgv_refined_multi_params base multi failure ghost)) h,
      nwState (mgv_deghost net) h = nwState net h.
  Proof.
    unfold mgv_deghost.
    intros.
    simpl.
    destruct net. auto.
  Qed.

  Lemma commit_invariant_lower_commit_recorded_committed :
    forall net : ghost_log_network,
      msg_refined_raft_intermediate_reachable net ->
      commit_invariant net ->
      commit_recorded_committed (mgv_deghost net).
  Proof.
    unfold commit_invariant, commit_recorded_committed, commit_recorded, commit_invariant_host.
    intuition;
    repeat find_rewrite_lem deghost_spec;
    repeat find_rewrite_lem msg_deghost_spec';
    rewrite msg_deghost_spec';
    apply lifted_committed_committed; auto.
    eauto using le_trans, msg_lifted_lastApplied_le_commitIndex.
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

  Lemma lifted_committed_log_allEntries_preserved :
    forall net net' e t,
      lifted_committed net e t ->
      (forall h e',
          In e' (log (snd (nwState net h))) ->
          In e' (log (snd (nwState net' h)))) ->
      (forall h e' t',
          In (t', e') (allEntries (fst (nwState net h))) ->
          In (t', e') (allEntries (fst (nwState net' h)))) ->
      lifted_committed net' e t.
  Proof.
    intros.
    find_apply_lem_hyp lifted_committed_committed.
    find_eapply_lem_hyp committed_log_allEntries_preserved; eauto.
    apply committed_lifted_committed.
    eapply committed_log_allEntries_preserved; eauto;
    intros;
    repeat find_rewrite_lem msg_deghost_spec;
    rewrite msg_deghost_spec; auto.
  Qed.

  Lemma lift_max_index_sanity :
    forall (net : ghost_log_network) h,
      msg_refined_raft_intermediate_reachable net ->
      maxIndex_sanity (deghost (mgv_deghost net)) ->
      lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h))) /\
      commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h))).
  Proof.
    intros.
    match goal with
      | [ H : _, H' : _ |- _ ] => apply H in H'; clear H
    end.
    unfold maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex in *.
    break_and.
    repeat match goal with
           | [ H : _ |- _ ] => specialize (H h)
           end.
    repeat find_rewrite_lem deghost_spec.
    repeat find_rewrite_lem msg_deghost_spec'.
    auto.
  Qed.

  Lemma haveNewEntries_log :
    forall es st st',
      log st = log st' ->
      haveNewEntries st es = true ->
      haveNewEntries st' es = true.
  Proof.
    unfold haveNewEntries.
    intros.
    find_rewrite. auto.
  Qed.

  Lemma hCR_preserves_committed :
    forall (net net' : ghost_log_network) h client id c out d l e t,
      handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) ->
      (forall h', nwState net' h' = update (nwState net) h (update_elections_data_client_request h (nwState net h) client id c, d) h') ->
      lifted_committed net e t ->
      lifted_committed net' e t.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; simpl; eauto.
    - intros. find_higher_order_rewrite.
      update_destruct; eauto using handleClientRequest_preservers_log.
    - intros. find_higher_order_rewrite.
      update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
  Qed.

  Lemma not_empty_intro :
    forall A (l : list A),
      l <> [] -> not_empty l = true.
  Proof.
    unfold not_empty.
    intros.
    break_match; congruence.
  Qed.

  Lemma haveNewEntries_true_intro :
    forall st es,
      es <> [] ->
      (forall e, findAtIndex (log st) (maxIndex es) = Some e ->
            eTerm e <> maxTerm es) ->
      haveNewEntries st es = true.
  Proof.
    unfold haveNewEntries.
    intros.
    do_bool. split.
    - auto using not_empty_intro.
    - break_match; auto.
      apply Bool.negb_true_iff.
      do_bool. intuition eauto.
  Qed.

  Definition lifted_prevLog_leader_sublog (net : network) : Prop :=
    forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      type (snd (nwState net leader)) = Leader ->
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      currentTerm (snd (nwState net leader)) = prevLogTerm ->
      0 < prevLogIndex ->
      0 < prevLogTerm ->
      exists ple, eIndex ple = prevLogIndex /\
             eTerm ple = prevLogTerm /\
             In ple (log (snd (nwState net leader))).

  Lemma prevLog_leader_sublog_lifted :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_prevLog_leader_sublog net.
  Proof.
    intros.
    pose proof (msg_lift_prop _ (lift_prop _ prevLog_leader_sublog_invariant)).
    find_insterU. conclude_using eauto.
    unfold prevLog_leader_sublog, lifted_prevLog_leader_sublog in *.
    intros.
    find_apply_lem_hyp in_mgv_ghost_packet.
    find_apply_lem_hyp in_ghost_packet.
    unfold deghost in *. simpl in *. break_match. simpl in *. subst.
    specialize (H0 leader).
    destruct (nwState leader). simpl in *.
    eauto.
  Qed.

  Lemma commit_invariant_client_request :
    forall h (net : ghost_log_network) st' ps' gd out d l client id c,
      handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) ->
      gd = update_elections_data_client_request h (nwState net h) client id c ->
      commit_invariant net ->
      maxIndex_sanity (deghost (mgv_deghost net)) ->
      msg_refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h (add_ghost_msg (params := ghost_log_params) h (nwState net h) l))) ->
      commit_invariant (mkNetwork ps' st').
  Proof.
    unfold msg_refined_raft_net_invariant_client_request, commit_invariant.
    intros. split.
    - { unfold commit_invariant_host in *. break_and.
        unfold commit_recorded_committed, commit_recorded in *.
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
              by (now erewrite <- handleClientRequest_commitIndex by eauto)
        end.
        update_destruct.
        - find_copy_apply_lem_hyp handleClientRequest_log.
          break_and. break_or_hyp.
          + repeat find_rewrite.
            eapply lifted_committed_log_allEntries_preserved; eauto.
            * simpl. intros. find_higher_order_rewrite.
              update_destruct; repeat find_rewrite; auto.
            * simpl. intros. find_higher_order_rewrite.
              update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
          + break_exists. break_and. repeat find_rewrite.
            simpl in *.
            match goal with
              | [ H : _ \/ In _ _ |- _ ] => invc H
            end.
            * find_eapply_lem_hyp (lift_max_index_sanity net h0); auto.
              break_and. simpl in *. omega.
            * { eapply lifted_committed_log_allEntries_preserved; eauto.
                - simpl. intros. find_higher_order_rewrite.
                  update_destruct; repeat find_rewrite; auto.
                  find_reverse_rewrite.
                  eapply handleClientRequest_preservers_log; eauto.
                - simpl. intros. find_higher_order_rewrite.
                  update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
              }
        - eapply lifted_committed_log_allEntries_preserved; eauto.
          + simpl. intros. find_higher_order_rewrite.
            update_destruct; repeat find_rewrite; eauto using handleClientRequest_preservers_log.
          + simpl. intros. find_higher_order_rewrite.
            update_destruct; eauto using update_elections_data_client_request_preserves_allEntries.
      }
    - unfold commit_invariant_nw in *.
      simpl. intros.
      find_apply_hyp_hyp.
      intuition.
      + eapply hCR_preserves_committed; eauto. simpl. subst. auto.
      + unfold send_packets in *.
        do_in_map.
        unfold add_ghost_msg in *.
        do_in_map.
        subst. simpl in *.
        exfalso. eapply handleClientRequest_no_append_entries; eauto 10.
  Qed.

  Lemma handleTimeout_preserves_committed :
    forall h (net net' : ghost_log_network) out d' l e t,
      handleTimeout h (snd (nwState net h)) = (out, d', l) ->
      (forall h', nwState net' h' = update (nwState net) h (update_elections_data_timeout h (nwState net h), d') h') ->
      lifted_committed net e t ->
      lifted_committed net' e t.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto.
    - intros. repeat find_higher_order_rewrite. update_destruct.
      + now erewrite handleTimeout_log_same by eauto.
      + auto.
    - intros. repeat find_higher_order_rewrite. update_destruct.
      + now rewrite update_elections_data_timeout_allEntries.
      + auto.
  Qed.

  Lemma lifted_committed_monotonic :
    forall net t t' e,
      lifted_committed net e t ->
      t <= t' ->
      lifted_committed net e t'.
  Proof.
    unfold lifted_committed.
    intros.
    break_exists_exists.
    intuition.
  Qed.


  Lemma commit_invariant_timeout :
    msg_refined_raft_net_invariant_timeout commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_timeout, commit_invariant.
    simpl. intuition.
    - unfold commit_invariant_host in *.
      simpl. intros.
      repeat find_higher_order_rewrite.
      update_destruct.
      + eapply handleTimeout_preserves_committed; eauto.
        match goal with
        | [ H : context [commitIndex] |- _ ] => erewrite handleTimeout_commitIndex in H by eauto
        end.
        match goal with
        | [ H : context [log] |- _ ] => erewrite handleTimeout_log_same in H by eauto
        end.
        eapply lifted_committed_monotonic; [eauto|].
        find_apply_lem_hyp handleTimeout_type_strong.
        intuition; repeat find_rewrite; auto.
      + eapply handleTimeout_preserves_committed; eauto.
    - unfold commit_invariant_nw in *.
      simpl. intros.
      find_apply_hyp_hyp.
      intuition.
      * eapply handleTimeout_preserves_committed; eauto.
        simpl. intros. subst. auto.
      * do_in_map.
        subst. simpl in *.
        unfold add_ghost_msg in *.
        do_in_map.
        subst. simpl in *.
        find_eapply_lem_hyp handleTimeout_packets; eauto.
        exfalso. eauto 10.
  Qed.

  Lemma committed_ext :
    forall ps  st st' t e,
      (forall h, st' h = st h) ->
      committed (mkNetwork ps st) e t ->
      committed (mkNetwork ps st') e t.
  Proof.
    unfold committed, directly_committed.
    simpl. intros.
    break_exists_exists.
    find_higher_order_rewrite.
    intuition.
    break_exists_exists.  intuition.
    find_higher_order_rewrite. auto.
  Qed.

  Lemma lifted_committed_ext :
    forall ps st st' t e,
      (forall h, st' h = st h) ->
      lifted_committed (mkNetwork ps st) e t ->
      lifted_committed (mkNetwork ps st') e t.
  Proof.
    intros.
    apply committed_lifted_committed.
    find_apply_lem_hyp lifted_committed_committed.
    unfold mgv_deghost in *.
    eauto using committed_ext.
  Qed.

  Definition lifted_state_machine_safety_nw' net :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit e t',
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      lifted_committed net e t' ->
      t >= t' ->
      (prevLogIndex > eIndex e \/
       (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/
       eIndex e > maxIndex entries \/
       In e entries).

  Lemma lifted_state_machine_safety_nw'_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_state_machine_safety_nw' net.
  Proof.
    intros.
    unfold lifted_state_machine_safety_nw'.
    intros.
    find_apply_lem_hyp lifted_committed_committed.
    find_apply_lem_hyp in_mgv_ghost_packet.
    match goal with
      | _ : snd (pBody ?p) = ?x |- _ =>
        assert (pBody (@mgv_deghost_packet _ _ _ ghost_log_params p) = x)
          by (rewrite pBody_mgv_deghost_packet; auto)
    end.
    eapply state_machine_safety'_invariant; eauto.
    eapply msg_lift_prop; eauto.
  Qed.

  Lemma lifted_entries_sorted_nw :
    forall net p t n pli plt es ci,
      msg_refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      sorted es.
  Proof.
    intros.
    find_apply_lem_hyp in_mgv_ghost_packet.
    match goal with
      | _ : snd (pBody ?p) = ?x |- _ =>
        assert (pBody (@mgv_deghost_packet _ _ _ ghost_log_params p) = x)
          by (rewrite pBody_mgv_deghost_packet; auto)
    end.
    find_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
    eapply msg_lift_prop; eauto.
  Qed.
      
  Lemma update_elections_data_appendEntries_preserves_allEntries' :
    forall st h t n pli plt es ci x,
      In x (allEntries (fst st)) ->
      In x (allEntries (update_elections_data_appendEntries h st t n pli plt es ci)).
  Proof.
    unfold update_elections_data_appendEntries.
    intros. break_let. break_match; auto.
    break_if; auto.
    simpl. intuition.
  Qed.

  Lemma lifted_transitive_commit_invariant :
    forall net h e e' t,
      msg_refined_raft_intermediate_reachable net ->
      In e (log (snd (nwState net h))) ->
      In e' (log (snd (nwState net h))) ->
      eIndex e <= eIndex e' ->
      lifted_committed net e' t ->
      lifted_committed net e t.
  Proof.
    intros.
    apply committed_lifted_committed.
    find_apply_lem_hyp lifted_committed_committed.
    repeat match goal with
             | H : _ |- _ =>
               rewrite <- msg_deghost_spec with (net0 := net) in H
           end.
    eapply transitive_commit_invariant; eauto.
    eapply msg_lift_prop; eauto.
  Qed.
  
  Lemma handleAppendEntries_preserves_commit :
    forall net net' h p t n pli plt es ci d m e t',
      msg_refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) ->
      (forall h', nwState net' h' = update (nwState net) h
                                      (update_elections_data_appendEntries
                                         h (nwState net h) t n pli plt es ci, d) h') ->
      lifted_committed net e t' ->
      lifted_committed net' e t'.
  Proof.
    intros.
    unfold lifted_committed in *.
    break_exists_name host. break_exists_name e'.
    exists host, e'.
    intuition.
    - (* directly committed doesn't change *)
      unfold lifted_directly_committed in *.
      break_exists_exists; intuition.
      find_higher_order_rewrite.
      update_destruct; eauto using update_elections_data_appendEntries_preserves_allEntries'.
    - (* e is still around *)
      find_higher_order_rewrite.
      update_destruct; simpl in *; eauto.
      assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by
            (unfold lifted_committed;
             exists host, e'; intuition;
             eapply lifted_no_entries_past_current_term_host_invariant; eauto).
      find_eapply_lem_hyp handleAppendEntries_log_detailed. intuition; repeat find_rewrite; eauto.
      + (* pli = 0, no entry at maxIndex es *)
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        assert (eIndex e > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
        intuition; try omega.
        find_copy_eapply_lem_hyp msg_lifted_sorted_host.
        exfalso.
	enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by
            (break_exists;
             intuition; eapply findAtIndex_None; eauto).
        eapply contiguous_range_exact_lo_elim_exists;
          [apply lifted_entries_contiguous_invariant; auto|].
        intuition.
        * find_apply_lem_hyp maxIndex_non_empty.
          break_exists; intuition; repeat find_rewrite.
          enough (eIndex x > 0) by omega.
          eapply lifted_entries_contiguous_nw_invariant; eauto.
        * enough (eIndex e <= maxIndex (log (snd (nwState net host)))) by omega.
          apply maxIndex_is_max; auto.
      + (* pli = 0, bad entry at maxIndex es *)
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        assert (eIndex e > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
        intuition; try omega.
        break_exists. intuition.
        find_apply_lem_hyp maxIndex_non_empty.
        break_exists_name maxEntry; intuition.
        repeat find_rewrite.
        find_false.
        f_equal.
        find_apply_lem_hyp findAtIndex_elim.
        intuition.
        eapply uniqueIndices_elim_eq; [| |eauto|];
        eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
        match goal with
          | |- In ?e _ =>
            assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by
                (unfold lifted_committed;
                 exists host, e'; intuition;
                 eapply lifted_no_entries_past_current_term_host_invariant; eauto)
        end.
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        assert (eIndex x > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
        intuition; omega.
      + find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        intuition;
          try solve
              [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega];
          [idtac].
        find_copy_eapply_lem_hyp msg_lifted_sorted_host.
        exfalso.
	enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by
            (break_exists;
             intuition; eapply findAtIndex_None; eauto).
        eapply contiguous_range_exact_lo_elim_exists;
          [apply lifted_entries_contiguous_invariant; auto|].
        intuition.
        * find_apply_lem_hyp maxIndex_non_empty.
          break_exists; intuition; repeat find_rewrite.
          enough (eIndex x0 > 0) by omega.
          enough (eIndex x0 > pli) by omega.
          eapply lifted_entries_contiguous_nw_invariant; eauto.
        * enough (eIndex e <= maxIndex (log (snd (nwState net host)))) by omega.
          apply maxIndex_is_max; auto.
      + find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        intuition;
          try solve
              [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega];
          [idtac].
        break_exists. intuition.
        find_apply_lem_hyp maxIndex_non_empty.
        break_exists_name maxEntry; intuition.
        repeat find_rewrite.
        find_false.
        f_equal.
        find_apply_lem_hyp findAtIndex_elim.
        intuition.
        eapply uniqueIndices_elim_eq; [| |eauto|];
        eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
        match goal with
          | |- In ?e _ =>
            assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by
                (unfold lifted_committed;
                 exists host, e'; intuition;
                 eapply lifted_no_entries_past_current_term_host_invariant; eauto)
        end.
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        intuition; try omega;
        enough (pli < eIndex maxEntry) by omega;
        eapply lifted_entries_contiguous_nw_invariant; eauto.
    - find_higher_order_rewrite.
      update_destruct; simpl in *; eauto.
      assert (lifted_committed net e' (currentTerm (snd (nwState net host)))) by
            (unfold lifted_committed;
             exists host, e'; intuition;
             eapply lifted_no_entries_past_current_term_host_invariant; eauto).
      find_eapply_lem_hyp handleAppendEntries_log_detailed. intuition; repeat find_rewrite; eauto.
      + (* pli = 0, no entry at maxIndex es *)
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        assert (eIndex e' > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
        intuition; try omega.
        find_copy_eapply_lem_hyp msg_lifted_sorted_host.
        exfalso.
	enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by
            (break_exists;
             intuition; eapply findAtIndex_None; eauto).
        eapply contiguous_range_exact_lo_elim_exists;
          [apply lifted_entries_contiguous_invariant; auto|].
        intuition.
        * find_apply_lem_hyp maxIndex_non_empty.
          break_exists; intuition; repeat find_rewrite.
          enough (eIndex x > 0) by omega.
          eapply lifted_entries_contiguous_nw_invariant; eauto.
        * enough (eIndex e' <= maxIndex (log (snd (nwState net host)))) by omega.
          apply maxIndex_is_max; auto.
      + (* pli = 0, bad entry at maxIndex es *)
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        assert (eIndex e' > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
        intuition; try omega.
        break_exists. intuition.
        find_apply_lem_hyp maxIndex_non_empty.
        break_exists_name maxEntry; intuition.
        repeat find_rewrite.
        find_false.
        f_equal.
        find_apply_lem_hyp findAtIndex_elim.
        intuition.
        eapply uniqueIndices_elim_eq; [| |eauto|];
        eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
        match goal with
          | |- In ?e _ =>
            assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by
                (unfold lifted_committed;
                 exists host, e'; intuition;
                 eapply lifted_no_entries_past_current_term_host_invariant; eauto)
        end.
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        assert (eIndex x > 0) by (eapply lifted_entries_gt_0_invariant; eauto).
        intuition; omega.
      + find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        intuition;
          try solve
              [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega];
          [idtac].
        find_copy_eapply_lem_hyp msg_lifted_sorted_host.
        exfalso.
	enough (exists e, eIndex e = (maxIndex es) /\ In e (log (snd (nwState net host)))) by
            (break_exists;
             intuition; eapply findAtIndex_None; eauto).
        eapply contiguous_range_exact_lo_elim_exists;
          [apply lifted_entries_contiguous_invariant; auto|].
        intuition.
        * find_apply_lem_hyp maxIndex_non_empty.
          break_exists; intuition; repeat find_rewrite.
          enough (eIndex x0 > 0) by omega.
          enough (eIndex x0 > pli) by omega.
          eapply lifted_entries_contiguous_nw_invariant; eauto.
        * enough (eIndex e' <= maxIndex (log (snd (nwState net host)))) by omega.
          apply maxIndex_is_max; auto.
      + find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        intuition;
          try solve
              [apply in_app_iff; right; apply removeAfterIndex_le_In; auto; omega];
          [idtac].
        break_exists. intuition.
        find_apply_lem_hyp maxIndex_non_empty.
        break_exists_name maxEntry; intuition.
        repeat find_rewrite.
        find_false.
        f_equal.
        find_apply_lem_hyp findAtIndex_elim.
        intuition.
        eapply uniqueIndices_elim_eq; [| |eauto|];
        eauto using sorted_uniqueIndices,lifted_entries_sorted_nw.
        match goal with
          | |- In ?e _ =>
            assert (lifted_committed net e (currentTerm (snd (nwState net host)))) by
                (unfold lifted_committed;
                 exists host, e'; intuition;
                 eapply lifted_no_entries_past_current_term_host_invariant; eauto)
        end.
        find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
        intuition; try omega;
        enough (pli < eIndex maxEntry) by omega;
        eapply lifted_entries_contiguous_nw_invariant; eauto.
  Qed.

  Lemma handleAppendEntries_currentTerm_le :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      currentTerm st <= currentTerm st'.
  Proof.
    intros.
    unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; find_inversion; simpl in *;
    do_bool; auto.
  Qed.

  Theorem handleAppendEntries_log_detailed :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      (commitIndex st' = commitIndex st /\ log st' = log st) \/
      (leaderId st' <> None /\
       currentTerm st' = t /\
       commitIndex st' = max (commitIndex st) (min ci (maxIndex es)) /\
       es <> nil /\
       pli = 0 /\ t >= currentTerm st /\ log st' = es /\
      haveNewEntries st es = true ) \/
      (leaderId st' <> None /\
       currentTerm st' = t /\
       commitIndex st' = max (commitIndex st)
                             (min ci (maxIndex (es ++ (removeAfterIndex (log st) pli)))) /\
       es <> nil /\
        exists e,
         In e (log st) /\
         eIndex e = pli /\
         eTerm e = plt) /\
      t >= currentTerm st /\
      log st' = es ++ (removeAfterIndex (log st) pli) /\
      haveNewEntries st es = true.
  Proof.
    intros. unfold handleAppendEntries in *.
    break_if; [find_inversion; subst; eauto|].
    break_if;
      [do_bool; break_if; find_inversion; subst;
        try find_apply_lem_hyp haveNewEntries_true;
        simpl in *; intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex, some_none, advanceCurrentTerm_term|].
    simpl in *. intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex.
    break_match; [|find_inversion; subst; eauto].
    break_if; [find_inversion; subst; eauto|].
    break_if; [|find_inversion; subst; eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex].
    find_inversion; subst; simpl in *.
    right. right.
    find_apply_lem_hyp findAtIndex_elim.
    intuition; do_bool; find_apply_lem_hyp haveNewEntries_true;
    intuition eauto using advanceCurrentTerm_term; congruence.
  Qed.

  Definition lifted_entries_gt_0_nw (net : ghost_log_network) : Prop :=
    forall p t n pli plt es ci e,
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      In e es ->
      eIndex e > 0.

  Lemma lifted_entries_gt_0_nw_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_gt_0_nw net.
  Proof.
    unfold lifted_entries_gt_0_nw.
    intros.
    pose proof msg_lift_prop _ entries_gt_0_nw_invariant _ $(eauto)$.
    unfold entries_gt_0_nw in *.
    find_apply_lem_hyp in_mgv_ghost_packet.
    match goal with
    | [ H : _ |- _ ] => eapply H; eauto
    end.
  Qed.

  Definition lifted_entries_sorted_nw (net : ghost_log_network) :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      sorted es.

  Lemma lifted_entries_sorted_nw_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_sorted_nw net.
  Proof.
    intros.
    pose proof msg_lift_prop _ entries_sorted_nw_invariant.
    find_copy_apply_hyp_hyp.
    unfold entries_sorted_nw, lifted_entries_sorted_nw in *.
    intros.
    find_apply_lem_hyp in_mgv_ghost_packet.
    eapply_prop_hyp In In; eauto.
  Qed.

  Lemma commit_invariant_append_entries :
    forall xs p ys (net : ghost_log_network) st' ps' gd d m t n pli plt es ci,
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) ->
      gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      commit_invariant net ->
      msg_refined_raft_intermediate_reachable net ->
      lifted_maxIndex_sanity net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' ->
             In p' (xs ++ ys) \/ p' = mkPacket (pDst p) (pSrc p)
                                             (write_ghost_log (pDst p) (nwState net (pDst p)), m)) ->
      commit_invariant (mkNetwork ps' st').
  Proof.
    unfold commit_invariant.
    intros.

    assert (In p (nwPackets net)) by (repeat find_rewrite; auto with *).
    split.
    - break_and.
       match goal with
       | [ H : commit_invariant_host _ |- _ ] =>
         rename H into Hhost;
           unfold commit_invariant_host in *
       end.
       simpl. intros.
       eapply lifted_committed_ext; eauto.

       match goal with
       | [ H : forall _, _ = _ |- _ ] => rewrite H in *
       end.
       update_destruct.
       + (* e is in h's log *)
         find_copy_apply_lem_hyp handleAppendEntries_log_detailed.
         break_or_hyp.
         * break_and. repeat find_rewrite.
           eapply lifted_committed_monotonic; [
               solve [eapply handleAppendEntries_preserves_commit; eauto] |
               solve [eauto using handleAppendEntries_currentTerm_le] ].
         * { break_or_hyp; repeat break_and.
             - (* beginning of time case *)
               repeat match goal with
               | [ H : _ <= _, H': _ |- _ ] => rewrite H' in H
               end.
               find_apply_lem_hyp NPeano.Nat.max_le. break_or_hyp.
               + (* my log is just the entries in the incoming AE.
                    so e was in the incoming entries.
                    but eIndex e <= old commit index.
                    by maxIndex_commitIndex, exists e' in old log such that eIndex e = eIndex e'.
                    note that e' is committed in the pre state by IH.
                    now apply SMS'_nw invariant to e' to get four cases.
                    first three are absurd by index calculation.
                    it follows that e' is in es.
                    but our new log is just es, so e' is in the new log.
                    by thus e = e' by unique indices.
                    thus e is committed.
                  *)
                 assert (eIndex e > 0) by (eapply lifted_entries_gt_0_nw_invariant; eauto).
                 assert (exists e', eIndex e' = eIndex e /\ In e' (log (snd (nwState net (pDst p))))).
                 {
                   eapply contiguous_range_exact_lo_elim_exists.
                   - eapply lifted_entries_contiguous_invariant. auto.
                   - split.
                     + auto.
                     + eapply le_trans; [eauto|].
                       eapply_prop lifted_maxIndex_sanity.
                 }
                 break_exists_name e'.
                 break_and.
                 assert (lifted_committed net e' (currentTerm (snd (nwState net (pDst p))))) as He'committed
                        by (apply Hhost; [auto|congruence]) .

                 find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
                 concludes.
                 assert (sorted (log d)) by (eauto using lifted_handleAppendEntries_logs_sorted).
                 intuition.
                 * omega.
                 * omega.
                 * match goal with
                   | [ H : _ |- _ ] => eapply maxIndex_is_max in H; eauto; [idtac]
                   end.
                   omega.
                 * assert (e = e') by (eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices).
                   subst.
                   eapply lifted_committed_monotonic; [
                       solve [eapply handleAppendEntries_preserves_commit; eauto] |
                       solve [eauto using handleAppendEntries_currentTerm_le] ].
               + (* eIndex e <= incoming ci.
                    result follows by the network invariant. *)
                 match goal with
                 | [ H : commit_invariant_nw _ |- _ ] =>
                   rename H into Hnet; unfold commit_invariant_nw in *
                 end.
                 eapply_prop_hyp In In; [| eauto | | eauto using Min.min_glb_l].
                 * eapply handleAppendEntries_preserves_commit; eauto.
                 * find_eapply_lem_hyp ghost_log_correct_invariant; eauto.
                   conclude_using eauto.
                   { intuition.
                     - match goal with
                       | [ H : In _ _, H' : _ |- _ ] => rewrite H' in H
                       end. auto.
                     - break_exists. break_and.
                       pose proof log_properties_hold_on_ghost_logs_invariant _ $(eauto)$ as Hprop.
                       unfold log_properties_hold_on_ghost_logs in *.
                       unfold msg_log_property in *.
                       specialize (Hprop (fun l => forall e, In e l -> eIndex e > 0) p).
                       conclude_using ltac:(intros; eapply lifted_entries_gt_0_invariant; eauto).
                       concludes. simpl in *.
                       find_apply_hyp_hyp.
                       omega.
                   }
             - (* middle of time case *)
               break_exists_name ple. break_and.
               repeat match goal with
                      | [ H : _ <= _, H': _ |- _ ] => rewrite H' in H
                      end.
               find_apply_lem_hyp NPeano.Nat.max_le. break_or_hyp.
               + (* eIndex e <= old commit index *)
                 repeat find_rewrite.
                 match goal with
                 | [ H : In e (_ ++ _) |- _ ] => apply in_app_or in H; destruct H
                 end.
                 * (* e is new *)
                   { assert (eIndex e > 0) by (eapply lifted_entries_gt_0_nw_invariant; eauto).
                     assert (exists e', eIndex e' = eIndex e /\ In e' (log (snd (nwState net (pDst p))))).
                     {
                       eapply contiguous_range_exact_lo_elim_exists.
                       - eapply lifted_entries_contiguous_invariant. auto.
                       - split.
                         + auto.
                         + eapply le_trans; [eauto|].
                           eapply_prop lifted_maxIndex_sanity.
                     }
                     break_exists_name e'.
                     break_and.
                     assert (lifted_committed net e' (currentTerm (snd (nwState net (pDst p))))) as He'committed
                         by (apply Hhost; [auto|congruence]) .

                     find_copy_eapply_lem_hyp lifted_state_machine_safety_nw'_invariant; eauto.
                     concludes.
                     assert (sorted es) by
                         (eapply lifted_entries_sorted_nw_invariant; eauto).
                     assert (contiguous_range_exact_lo es (eIndex ple)) by
                         (eapply lifted_entries_contiguous_nw_invariant; eauto).
                     find_eapply_lem_hyp contiguous_range_exact_lo_elim_lt; eauto.
                     intuition.
                     * omega.
                     * omega.
                     * match goal with
                       | [ H : _ |- _ ] => eapply maxIndex_is_max in H; eauto with *; [idtac]
                       end.
                       omega.
                     * assert (e = e') by (eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices).
                       subst.
                       eapply lifted_committed_monotonic; [
                           solve [eapply handleAppendEntries_preserves_commit; eauto] |
                           solve [eauto using handleAppendEntries_currentTerm_le] ].
                   }
                 * (* e is old *)
                   { eapply lifted_committed_monotonic.
                     - eapply handleAppendEntries_preserves_commit; eauto.
                       eapply Hhost with (h := pDst p); eauto using removeAfterIndex_in.
                     - eauto using handleAppendEntries_currentTerm_le.
                   }
               + (* eIndex e <= new commit index *)
                 match goal with
                 | [ H : In e _ |- _ ] =>
                   repeat match goal with
                   | [ H' : _ |- _ ] => rewrite H' in H
                   end;
                     apply in_app_or in H; destruct H
                 end.
                 * (* e is new *)
                   (* follows from network invariant *)
                   { match goal with
                     | [ H : commit_invariant_nw _ |- _ ] =>
                       rename H into Hnet; unfold commit_invariant_nw in *
                     end.
                     match goal with
                     | [ H : In _ (nwPackets _), H' : _ |- _ ] => eapply H' in H
                     end; [| eauto | | eauto using Min.min_glb_l].
                     * eapply handleAppendEntries_preserves_commit; eauto.
                     * find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto.
                       conclude_using eauto.
                       { intuition.
                         - match goal with
                           | [ H : In _ _, H' : _ |- _ ] => rewrite H' in H
                           end. auto.
                         - break_exists_name gple. break_and.
                           subst.
                           eauto using findGtIndex_in.
                       }
                   }

                 * (* e is old *)
                   (* eIndex e <= pli
                      by ghost log contiguous, exists e' in ghost log such that eIndex e = eIndex e'.
                      e' is committed by the nw invariant.
                      by ghost log matching, e = e'.
                      thus e is committed.
                    *)
                   assert (eIndex e <= eIndex ple) by
                       (eapply removeAfterIndex_In_le; eauto using msg_lifted_sorted_host).
                   pose proof log_properties_hold_on_ghost_logs_invariant _ $(eauto)$ as Hprop.
                   unfold log_properties_hold_on_ghost_logs in *.
                   unfold msg_log_property in *.
                   specialize (Hprop (fun l => contiguous_range_exact_lo l 0) p).
                   conclude_using ltac:(intros; eapply lifted_entries_contiguous_invariant; eauto).
                   concludes.
                   simpl in *.

                   find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto.
                   conclude_using eauto.
                   { intuition.
                     - subst. find_apply_lem_hyp removeAfterIndex_in.
                       pose proof lifted_entries_gt_0_invariant _ $(eauto)$ _ _ $(eauto)$.
                       omega.
                     - break_exists_name gple. break_and.
                       assert (exists e', eIndex e' = eIndex e /\ In e' (fst (pBody p))).
                       {
                         eapply contiguous_range_exact_lo_elim_exists; eauto.
                         split.
                         + eapply lifted_entries_gt_0_invariant; eauto using removeAfterIndex_in.
                         + eapply le_trans with (m := eIndex gple); try omega.
                           apply maxIndex_is_max; auto.
                           pose proof log_properties_hold_on_ghost_logs_invariant _ $(eauto)$ as Hsort.
                           unfold log_properties_hold_on_ghost_logs in *.
                           unfold msg_log_property in *.
                           specialize (Hsort sorted p msg_lifted_sorted_host).
                           auto.
                       }
                       break_exists_name e'. break_and.
                       find_apply_lem_hyp removeAfterIndex_in.
                       assert (e = e').
                       {
                         eapply uniqueIndices_elim_eq;
                         eauto using msg_lifted_sorted_host, sorted_uniqueIndices.
                         pose proof ghost_log_entries_match_invariant _ $(eauto)$ (pDst p) _ $(eauto)$
                           as Hem.
                         specialize (Hem ple gple e').
                         repeat concludes. intuition.
                       }
                       subst.


                       match goal with
                       | [ H : commit_invariant_nw _ |- _ ] =>
                         rename H into Hnet; unfold commit_invariant_nw in *
                       end.
                       eapply handleAppendEntries_preserves_commit; eauto.
                       eapply Hnet; eauto using Min.min_glb_l.
                   }
           }
       + eapply handleAppendEntries_preserves_commit; eauto.
    - (* nw invariant preserved *)
      break_and.
      unfold commit_invariant_nw in *.
      simpl. intros.
      find_apply_hyp_hyp.
      intuition.
      + eapply handleAppendEntries_preserves_commit; eauto.
        simpl. subst. auto.
      + subst. simpl in *.
        find_apply_lem_hyp handleAppendEntries_not_append_entries.
        subst. exfalso. eauto 10.
  Qed.


  Lemma handleAppendEntriesReply_preserves_commit :
    forall (net net' : ghost_log_network) h src t es b st' l e t',
      handleAppendEntriesReply h (snd (nwState net h)) src t es b = (st', l) ->
      (forall h', nwState net' h' = update (nwState net) h (fst (nwState net h), st') h') ->
      lifted_committed net e t' ->
      lifted_committed net' e t'.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto.
    - intros. repeat find_higher_order_rewrite. update_destruct.
      + now erewrite handleAppendEntriesReply_same_log by eauto.
      + auto.
    - intros. repeat find_higher_order_rewrite. update_destruct; auto.
  Qed.

  Lemma commit_invariant_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_append_entries_reply, commit_invariant.
    simpl. intros.
    split.
    - unfold commit_invariant_host in *.
      simpl. intuition.
      repeat find_higher_order_rewrite.
      update_destruct.
      + eapply handleAppendEntriesReply_preserves_commit; eauto.
        match goal with
        | [ H : context [commitIndex] |- _ ] => erewrite handleAppendEntriesReply_same_commitIndex in H by eauto
        end.
        match goal with
        | [ H : context [log] |- _ ] => erewrite handleAppendEntriesReply_same_log in H by eauto
        end.
        eapply lifted_committed_monotonic; [eauto|].
        find_apply_lem_hyp handleAppendEntriesReply_type_term.
        intuition; repeat find_rewrite; auto.
      + eapply handleAppendEntriesReply_preserves_commit; eauto.
    - unfold commit_invariant_nw in *.
      simpl. intros.
      find_apply_hyp_hyp.
      intuition.
      + eapply handleAppendEntriesReply_preserves_commit; eauto.
        simpl. subst. auto.
      + do_in_map. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        find_apply_lem_hyp handleAppendEntriesReply_packets.
        subst. simpl in *. intuition.
  Qed.

  Lemma handleRequestVote_preserves_committed :
    forall (net net' : ghost_log_network) h t c li lt st' ms e t',
      handleRequestVote h (snd (nwState net h)) t c li lt = (st', ms) ->
      (forall h', nwState net' h' = update (nwState net) h (update_elections_data_requestVote h c t c li lt (nwState net h), st') h') ->
      lifted_committed net e t' ->
      lifted_committed net' e t'.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto.
    - intros. find_higher_order_rewrite. update_destruct.
      + now erewrite handleRequestVote_same_log by eauto.
      + auto.
    - intros. find_higher_order_rewrite. update_destruct.
      + now rewrite update_elections_data_requestVote_allEntries.
      + auto.
  Qed.

  Lemma commit_invariant_request_vote :
    msg_refined_raft_net_invariant_request_vote commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_request_vote, commit_invariant.
    simpl. intuition.
    - unfold commit_invariant_host in *.
      simpl. intros.
      repeat find_higher_order_rewrite.
      update_destruct.
      + eapply handleRequestVote_preserves_committed; eauto.
        match goal with
        | [ H : context [commitIndex] |- _ ] => erewrite handleRequestVote_same_commitIndex in H by eauto
        end.
        match goal with
        | [ H : context [log] |- _ ] => erewrite handleRequestVote_same_log in H by eauto
        end.
        eapply lifted_committed_monotonic; eauto.
        find_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
        intuition.
        unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
        simpl in *.
        repeat find_rewrite. auto.
      + eapply handleRequestVote_preserves_committed; eauto.
    - unfold commit_invariant_nw in *.
      simpl. intros.
      find_apply_hyp_hyp. intuition.
      + eapply handleRequestVote_preserves_committed; eauto.
        simpl. intros. subst. auto.
      + subst. simpl in *. unfold write_ghost_log in *.
        find_apply_lem_hyp handleRequestVote_no_append_entries.
        subst.
        exfalso. eauto 10.
  Qed.

  Lemma handleRequestVoteReply_preserves_committed :
    forall (net net' : ghost_log_network) h src t v st' e t',
      handleRequestVoteReply h (snd (nwState net h)) src t v = st' ->
      (forall h', nwState net' h' = update (nwState net) h
                                      (update_elections_data_requestVoteReply h
                                                                              src t v (nwState net h), st') h') ->
      lifted_committed net e t' ->
      lifted_committed net' e t'.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto.
    - intros. repeat find_higher_order_rewrite. update_destruct.
      + erewrite handleRequestVoteReply_log; eauto.
      + auto.
    - intros. repeat find_higher_order_rewrite. update_destruct.
      + rewrite update_elections_data_requestVoteReply_allEntries. auto.
      + auto.
  Qed.

  Lemma commit_invariant_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_request_vote_reply, commit_invariant.
    simpl. intuition.
    - unfold commit_invariant_host in *. simpl. intuition.
      match goal with
      | [ H : forall h, st' h = _ |- _ ] => repeat rewrite H in *
      end. destruct (name_eq_dec (pDst p) h).
      + subst h. subst gd. rewrite_update. simpl in *.
        eapply handleRequestVoteReply_preserves_committed; eauto.
        find_copy_apply_lem_hyp handleRequestVoteReply_type.
        subst.
        match goal with
        | [ H : context [commitIndex] |- _ ] => rewrite handleRequestVoteReply_same_commitIndex in H
        end.
        match goal with
        | [ H : context [log] |- _ ] => erewrite handleRequestVoteReply_same_log in H
        end.
        eapply lifted_committed_monotonic; eauto.
        intuition; repeat find_rewrite; auto.
      + rewrite_update. eapply handleRequestVoteReply_preserves_committed; eauto.
        simpl. subst. auto.
    - unfold commit_invariant_nw. simpl.
      intros.
      find_apply_hyp_hyp.
      eapply handleRequestVoteReply_preserves_committed; eauto.
      simpl. subst. auto.
  Qed.


  Lemma committed_ext' :
    forall ps ps' st st' t e,
      (forall h, st' h = st h) ->
      committed (mkNetwork ps st) e t ->
      committed (mkNetwork ps' st') e t.
  Proof.
    unfold committed, directly_committed.
    simpl. intros.
    break_exists_exists.
    find_higher_order_rewrite.
    intuition.
    break_exists_exists.  intuition.
    find_higher_order_rewrite. auto.
  Qed.

  Lemma lifted_committed_ext' :
    forall ps ps' st st' t e,
      (forall h, st' h = st h) ->
      lifted_committed (mkNetwork ps st) e t ->
      lifted_committed (mkNetwork ps' st') e t.
  Proof.
    intros.
    apply committed_lifted_committed.
    find_apply_lem_hyp lifted_committed_committed.
    unfold mgv_deghost in *.
    eauto using committed_ext'.
  Qed.

  Lemma doLeader_spec :
    forall st n os st' ms,
      doLeader st n = (os, st', ms) ->
      (st' = st /\ ms = []) \/
      (type st = Leader /\
       log st' = log st /\
       type st' = type st /\
       currentTerm st' = currentTerm st /\
       nextIndex st' = nextIndex st /\
       commitIndex st' = commitIndex (advanceCommitIndex st n) /\
       forall m, In m ms ->
            exists h, h <> n /\ m = replicaMessage (advanceCommitIndex st n) n h).
  Proof.
    unfold doLeader.
    intros.
    destruct st. simpl in *.
    repeat break_match; repeat find_inversion; simpl in *; eauto.
    right. intuition.
    - intros.
      do_in_map. subst.
      find_apply_lem_hyp filter_In. break_and.
      break_if; try discriminate.
      eexists. intuition eauto.
    - intuition.
  Qed.

  Lemma haveQuorum_directly_committed :
    forall net h e,
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net h)) = Leader ->
      In e (log (snd (nwState net h))) ->
      haveQuorum (snd (nwState net h)) h (eIndex e) = true ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      directly_committed net e.
  Proof.
    unfold haveQuorum, directly_committed.
    intros. do_bool.
    eexists. intuition eauto.
    - apply filter_NoDup. pose proof no_dup_nodes. simpl in *. auto.
    - find_apply_lem_hyp filter_In. break_and. do_bool.
      eapply match_index_all_entries_invariant; eauto.
  Qed.

  Lemma advanceCommitIndex_committed :
    forall h net,
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net h)) = Leader ->
      (forall e, In e (log (snd (nwState net h))) ->
            eIndex e <= commitIndex (snd (nwState net h)) ->
            committed net e (currentTerm (snd (nwState net h)))) ->
      (forall e, In e (log (snd (nwState net h))) ->
            eIndex e <= commitIndex (advanceCommitIndex (snd (nwState net h)) h) ->
            committed net e (currentTerm (snd (nwState net h)))).
  Proof.
    unfold advanceCommitIndex.
    intros. simpl in *.
    match goal with
    | [ H : context [fold_left Nat.max ?l ?x] |- _ ] =>
      pose proof fold_left_maximum_cases l x
    end. intuition.
    break_exists. break_and.
    find_apply_lem_hyp in_map_iff.
    break_exists_name witness. break_and.
    find_apply_lem_hyp filter_In.  break_and.
    find_apply_lem_hyp findGtIndex_necessary. do_bool. break_and. do_bool. break_and.
    do_bool.
    unfold committed.
    exists h, witness. intuition.
    eapply haveQuorum_directly_committed; eauto.
  Qed.

  Lemma lifted_advanceCommitIndex_lifted_committed :
    forall h net,
      msg_refined_raft_intermediate_reachable net ->
      type (snd (nwState net h)) = Leader ->
      (forall e, In e (log (snd (nwState net h))) ->
            eIndex e <= commitIndex (snd (nwState net h)) ->
            lifted_committed net e (currentTerm (snd (nwState net h)))) ->
      (forall e, In e (log (snd (nwState net h))) ->
            eIndex e <= commitIndex (advanceCommitIndex (snd (nwState net h)) h) ->
            lifted_committed net e (currentTerm (snd (nwState net h)))).
  Proof.
    intros.
    find_apply_lem_hyp msg_simulation_1.
    match goal with
    | [ H : refined_raft_intermediate_reachable _ |- _ ] =>
      eapply advanceCommitIndex_committed in H
    end;
      repeat rewrite msg_deghost_spec' in *;
      eauto using committed_lifted_committed, lifted_committed_committed.
  Qed.

  Lemma and_imp_2 :
    forall P Q : Prop,
      P /\ (P -> Q) -> P /\ Q.
  Proof.
    tauto.
  Qed.

  Lemma lifted_leaderLog_in_log :
    forall net leader ll e,
      msg_refined_raft_intermediate_reachable net ->
      In (currentTerm (snd (nwState net leader)), ll) (leaderLogs (fst (nwState net leader))) ->
      In e ll ->
      In e (log (snd (nwState net leader))).
  Proof.
        (* use lifted versions of LeadersHaveLeaderLogsStrong and OneLeaderLogPerTerm *)
  Admitted.


  Definition lifted_leaders_have_leaderLogs (net : ghost_log_network) : Prop :=
    forall h,
      type (snd (nwState net h)) = Leader ->
      exists ll,
        In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))).
  Lemma lifted_leaders_have_leaderLogs_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_leaders_have_leaderLogs net.
  Proof.
    intros.
    pose proof msg_lift_prop _ leaders_have_leaderLogs_invariant _ $(eauto)$.
    unfold leaders_have_leaderLogs, lifted_leaders_have_leaderLogs in *.
    intros.
    match goal with
    | [ H : _ |- _ ] => specialize (H h)
    end.
    repeat find_rewrite_lem msg_deghost_spec.
    auto.
  Qed.


  Definition lifted_leader_completeness_directly_committed (net : ghost_log_network) : Prop :=
    forall t e log h,
      lifted_directly_committed net e ->
      t > eTerm e -> In (t, log) (leaderLogs (fst (nwState net h))) -> In e log.

  Definition lifted_leader_completeness_committed (net : ghost_log_network) : Prop :=
    forall t t' e log h,
      lifted_committed net e t ->
      t' > t -> In (t', log) (leaderLogs (fst (nwState net h))) -> In e log.

  Definition lifted_leader_completeness (net : ghost_log_network) : Prop :=
    lifted_leader_completeness_directly_committed net /\
    lifted_leader_completeness_committed net.

  Lemma lifted_leader_completeness_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      lifted_leader_completeness net.
  Proof.
    intros.
    pose proof msg_lift_prop _ leader_completeness_invariant _ $(eauto)$.
    unfold lifted_leader_completeness, leader_completeness in *.
    intuition.
    - unfold lifted_leader_completeness_directly_committed, leader_completeness_directly_committed in *.
      intros.
      find_apply_lem_hyp lifted_directly_committed_directly_committed.
      eapply_prop_hyp directly_committed directly_committed; eauto.
      rewrite msg_deghost_spec'. eauto.
    - unfold lifted_leader_completeness_committed, leader_completeness_committed in *.
      intros.
      find_apply_lem_hyp lifted_committed_committed.
      eapply_prop_hyp committed committed; eauto.
      rewrite msg_deghost_spec'. eauto.
  Qed.

  Definition msg_lifted_leader_sublog_host (net : ghost_log_network) : Prop :=
    forall leader e h,
      type (snd (nwState net leader)) = Leader ->
      In e (log (snd (nwState net h))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).

  Lemma msg_lifted_leader_sublog_host_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      msg_lifted_leader_sublog_host net.
  Proof.
    intros.
    pose proof msg_lift_prop _ (lift_prop _ leader_sublog_invariant_invariant) _ $(eauto)$.
    simpl in *.
    unfold leader_sublog_invariant, leader_sublog_host_invariant, msg_lifted_leader_sublog_host in *.
    intuition.
    match goal with
    | [ H : _ |- _ ] =>
      specialize (H leader e h)
    end.
    repeat find_rewrite_lem deghost_spec.
    repeat find_rewrite_lem msg_deghost_spec.
    auto.
  Qed.

  Lemma lifted_entries_match_invariant :
    forall net h h',
      msg_refined_raft_intermediate_reachable net ->
      entries_match (log (snd (nwState net h))) (log (snd (nwState net h'))).
  Proof.
    intros.
    find_apply_lem_hyp msg_simulation_1.
    find_eapply_lem_hyp entries_match_invariant.
    repeat rewrite msg_deghost_spec' in *.
    eauto.
  Qed.

  Lemma commitIndex_anywhere :
    forall net leader h e,
      msg_refined_raft_intermediate_reachable net ->
      type (snd (nwState net leader)) = Leader ->
      In e (log (snd (nwState net leader))) ->
      eIndex e <= commitIndex (snd (nwState net h)) ->
      currentTerm (snd (nwState net h)) <= currentTerm (snd (nwState net leader)) ->
      lifted_maxIndex_sanity net ->
      commit_invariant_host net ->
      In e (log (snd (nwState net h))).
  Proof.
    intros.

    unfold lifted_maxIndex_sanity in *. break_and.
    pose proof lifted_entries_contiguous_invariant _ $(eauto)$ h.
    pose proof contiguous_range_exact_lo_elim_exists _ _ (eIndex e) $(eauto)$
         $(split; [solve [eapply lifted_entries_gt_0_invariant; eauto]| solve[eauto using le_trans]])$.
    break_exists_name e'. break_and.
    match goal with
    | [ H : commit_invariant_host _ |- _ ] =>
      unfold commit_invariant_host in H;
        specialize (H h e' $(auto)$ $(repeat find_rewrite; auto)$)
    end.
    unfold lifted_committed in *. break_exists_name h'. break_exists_name e''. break_and.
    assert (In e'' (log (snd (nwState net leader)))).
    {
      assert (eTerm e'' <= currentTerm (snd (nwState net leader))) by eauto using le_trans.
      find_apply_lem_hyp le_lt_or_eq. break_or_hyp.
      - find_copy_apply_lem_hyp lifted_leaders_have_leaderLogs_invariant; auto.
        break_exists_name ll.
        find_eapply_lem_hyp lifted_leaderLog_in_log; eauto.
        pose proof lifted_leader_completeness_invariant _ $(eauto)$.
        unfold lifted_leader_completeness in *. break_and.
        eapply_prop lifted_leader_completeness_directly_committed; eauto.
      - pose proof msg_lifted_leader_sublog_host_invariant _ $(eauto)$.
        unfold msg_lifted_leader_sublog_host in *.
        eauto.
    }

    pose proof lifted_entries_match_invariant _  h' leader $(eauto)$ e'' e'' e'.
    repeat concludes.
    intuition.
    assert (e = e').
    {
      eapply uniqueIndices_elim_eq;
      eauto  using sorted_uniqueIndices,  msg_lifted_sorted_host.
    }
    subst.
    auto.
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


  Lemma doLeader_preserves_committed :
    forall (net net' : ghost_log_network) d h os d' ms gd  e t,
      doLeader d h = (os, d', ms) ->
      nwState net h = (gd, d) ->
      (forall h', nwState net' h' = update (nwState net) h (gd, d') h') ->
      lifted_committed net e t ->
      lifted_committed net' e t.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto;
    intros; find_higher_order_rewrite; update_destruct.
    - intros. find_higher_order_rewrite.
      erewrite doLeader_same_log; eauto.
    - auto.
    - repeat find_rewrite. auto.
    - auto.
  Qed.

  Lemma doLeader_message_lci :
    forall st h os st' ms m t n pli plt es ci,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      ci = commitIndex st'.
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; intuition.
    do_in_map.
    unfold replicaMessage in *.
    simpl in *.
    repeat break_match; repeat find_inversion; subst; simpl in *;
    repeat find_inversion; auto.
  Qed.

  Lemma doLeader_message_term :
    forall st h os st' ms m t n pli plt es ci,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      snd m = AppendEntries t n pli plt es ci ->
      t = currentTerm st'.
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; intuition.
    do_in_map.
    subst.
    unfold replicaMessage in *. simpl in *.
    find_inversion.
    auto.
  Qed.


  Lemma commit_invariant_do_leader :
    forall net st' ps' gd d h os d' ms,
      doLeader d h = (os, d', ms) ->
      commit_invariant net ->
      msg_refined_raft_intermediate_reachable net ->
      lifted_maxIndex_sanity net ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p,
          In p ps' -> In p (nwPackets net) \/ In p (send_packets h (add_ghost_msg (params := ghost_log_params) h (gd, d) ms))) ->
      commit_invariant {| nwPackets := ps'; nwState := st' |}.
  Proof.
    unfold commit_invariant.
    simpl. intros. break_and.
    apply and_imp_2.
    split.
    - find_apply_lem_hyp doLeader_spec. break_or_hyp.
      + break_and.
        unfold commit_invariant_host in *. simpl. intros. repeat find_higher_order_rewrite.
        eapply lifted_committed_ext' with (ps := nwPackets net) (st := nwState net).
        * intros. subst. repeat find_higher_order_rewrite.
          match goal with
          | [ |- context [ update _ ?x _ ?y ] ] =>
            destruct (name_eq_dec x y); subst; rewrite_update
          end; auto.
        * match goal with
          | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
            replace x with (fst (nwState net h)) in * by (rewrite H; auto);
              replace y with (snd (nwState net h)) in * by (rewrite H; auto);
              clear H
          end.
          destruct net. simpl in *. auto.
          update_destruct; auto.
      + break_and.
        unfold commit_invariant_host in *.
        simpl. intros. repeat find_higher_order_rewrite.
        match goal with
        | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
          replace x with (fst (nwState net h)) in * by (rewrite H; auto);
            replace y with (snd (nwState net h)) in * by (rewrite H; auto);
            clear H
        end.
        match goal with
        | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
          destruct (name_eq_dec x y); subst; rewrite_update
        end.
        * { eapply lifted_committed_log_allEntries_preserved.
            - simpl. find_rewrite. eapply lifted_advanceCommitIndex_lifted_committed; auto.
              + simpl in *. repeat find_rewrite. auto.
              + simpl in *. repeat find_rewrite. auto.
            - simpl. intros. find_higher_order_rewrite.
              update_destruct.
              + repeat find_rewrite. auto.
              + auto.
            - simpl. intros. find_higher_order_rewrite.
              update_destruct; auto.
          }
        * { eapply lifted_committed_log_allEntries_preserved; eauto.
            + simpl. intros. find_higher_order_rewrite. update_destruct; repeat find_rewrite; auto.
            + simpl. intros. find_higher_order_rewrite. update_destruct; repeat find_rewrite; auto.
          }
    - intros Hhostpost.
      unfold commit_invariant_nw in *.
      simpl. intros.
      find_apply_hyp_hyp.
      intuition.
      + (* old packet *)
        eapply_prop_hyp In In; eauto.
        eauto using doLeader_preserves_committed.
      + (* new packet *)
        do_in_map. subst. simpl in *.
        unfold add_ghost_msg in *.
        do_in_map. subst. simpl in *.
        find_copy_eapply_lem_hyp doLeader_message_lci; eauto.
        find_copy_eapply_lem_hyp doLeader_message_term; eauto.
        unfold write_ghost_log in *.
        simpl in *.
        match goal with
        | [ H : In _ (log _) |- _ ] => erewrite <- doLeader_same_log in H by eauto
        end.
        unfold commit_invariant_host in *.
        simpl in *.
        specialize (Hhostpost h e).
        subst.
        repeat find_higher_order_rewrite.
        repeat rewrite_update.
        simpl in *.
        intuition.
  Qed.

  Lemma doGenericServer_preserves_committed :
    forall (net net' : ghost_log_network) h out st' ms e t,
      doGenericServer h (snd (nwState net h)) = (out, st', ms) ->
      (forall h', nwState net' h' = update (nwState net) h (fst (nwState net h), st') h') ->
      lifted_committed net e t ->
      lifted_committed net' e t.
  Proof.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto;
    intros; repeat find_higher_order_rewrite; update_destruct; auto.
    now erewrite doGenericServer_log by eauto.
  Qed.

  Lemma commit_invariant_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_do_generic_server, commit_invariant.
    simpl. intros.
    match goal with
    | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
      replace x with (fst (nwState net h)) in * by (rewrite H; auto);
        replace y with (snd (nwState net h)) in * by (rewrite H; auto);
        clear H
    end.
    intuition.
    - unfold commit_invariant_host in *.
      simpl. intros.
      repeat find_higher_order_rewrite.

      update_destruct.
      + eapply doGenericServer_preserves_committed; eauto.
        match goal with
        | [ H : context [commitIndex] |- _ ] => erewrite doGenericServer_commitIndex  in H  by eauto
        end.
        match goal with
        | [ H : context [log] |- _ ] => erewrite doGenericServer_log in H by eauto
        end.
        eapply lifted_committed_monotonic; eauto.
        find_apply_lem_hyp doGenericServer_type.
        intuition. repeat find_rewrite. auto.
      + eapply doGenericServer_preserves_committed; eauto.
    - unfold commit_invariant_nw in *.
      simpl. intuition.
      + find_apply_hyp_hyp. intuition.
        * eapply doGenericServer_preserves_committed; eauto.
        * do_in_map. unfold add_ghost_msg in *. do_in_map.
          find_apply_lem_hyp doGenericServer_packets.
          subst. simpl in *. intuition.
  Qed.

  Lemma commit_invariant_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_state_same_packet_subset, commit_invariant.
    intuition.
    - unfold commit_invariant_host in *. intros.
      repeat find_reverse_higher_order_rewrite.
      destruct net, net'. simpl in *.
      eapply lifted_committed_ext; [|eauto]. simpl. auto.
    - unfold commit_invariant_nw in *. intros.
      find_apply_hyp_hyp.
      destruct net, net'. simpl in *.
      eapply lifted_committed_ext'; [|eauto]. auto.
  Qed.

  Lemma reboot_preserves_committed :
    forall (net net' : ghost_log_network) h e t,
      (forall h', nwState net' h' = update (nwState net) h (fst (nwState net h), reboot (snd (nwState net h))) h') ->
      lifted_committed net e t ->
      lifted_committed net' e t.
  Proof.
    unfold reboot.
    intros.
    eapply lifted_committed_log_allEntries_preserved; eauto;
    intros; repeat find_higher_order_rewrite; update_destruct; auto.
  Qed.

  Lemma commit_invariant_reboot :
    msg_refined_raft_net_invariant_reboot commit_invariant.
  Proof.
    unfold msg_refined_raft_net_invariant_reboot, commit_invariant.
    intros.
    match goal with
    | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
      replace x with (fst (nwState net h)) in * by (rewrite H; auto);
        replace y with (snd (nwState net h)) in * by (rewrite H; auto);
        clear H
    end.
    intuition.
    - unfold commit_invariant_host in *.
      intros. repeat find_higher_order_rewrite.
      update_destruct; eapply reboot_preserves_committed; eauto.
    - unfold commit_invariant_nw in *.
      intros.
      unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
      simpl in *.
      repeat find_reverse_rewrite.
      eapply reboot_preserves_committed; eauto.
  Qed.

  Lemma maxIndex_sanity_lift :
    forall net,
      maxIndex_sanity (deghost (mgv_deghost net)) ->
      lifted_maxIndex_sanity net.
  Proof.
    unfold maxIndex_sanity, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intros. intuition;
    repeat match goal with
      | [ H : forall _, _, h : Net.name |- _ ] => specialize (H h)
    end;
    repeat find_rewrite_lem deghost_spec;
    repeat find_rewrite_lem msg_deghost_spec;
    auto.
  Qed.

  Lemma maxIndex_sanity_lower :
    forall net,
      lifted_maxIndex_sanity net ->
      maxIndex_sanity (deghost (mgv_deghost net)).
  Proof.
    unfold maxIndex_sanity, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
    intuition; rewrite deghost_spec; rewrite msg_deghost_spec';
    repeat match goal with
             | [ H : forall _, _, h : Net.name |- _ ] => specialize (H h)
           end; intuition.
  Qed.

  Definition everything (net : ghost_log_network) : Prop :=
    lifted_maxIndex_sanity net /\
    commit_invariant net /\
    state_machine_safety (deghost (mgv_deghost net)).

  Lemma everything_init :
    msg_refined_raft_net_invariant_init everything.
  Proof.
    unfold msg_refined_raft_net_invariant_init, everything.
    intuition.
    - apply lifted_maxIndex_sanity_init.
    - apply commit_invariant_init.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed; [constructor|].
        apply commit_invariant_init.
      + apply state_machine_safety'_invariant.
        constructor.
  Qed.

  Lemma everything_client_request :
    msg_refined_raft_net_invariant_client_request' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_client_request', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_client_request; eauto.
    - eapply commit_invariant_client_request; eauto.
      + auto using maxIndex_sanity_lower.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed; auto.
        eapply commit_invariant_client_request; eauto.
        apply maxIndex_sanity_lower. auto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_timeout :
    msg_refined_raft_net_invariant_timeout' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_timeout', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_timeout; eauto.
    - eapply commit_invariant_timeout; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_timeout; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_append_entries :
    msg_refined_raft_net_invariant_append_entries' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_append_entries', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_append_entries; eauto.
      intros.
      find_apply_hyp_hyp.
      intuition.
      right.
      subst.
      unfold mgv_deghost_packet. auto.
    - eapply commit_invariant_append_entries; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_append_entries; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_append_entries_reply', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_append_entries_reply; eauto.
    - eapply commit_invariant_append_entries_reply; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_append_entries_reply; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_request_vote :
    msg_refined_raft_net_invariant_request_vote' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_request_vote', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_request_vote; eauto.
    - eapply commit_invariant_request_vote; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_request_vote; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_request_vote_reply', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_request_vote_reply; eauto.
    - eapply commit_invariant_request_vote_reply; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_request_vote_reply; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_do_leader :
    msg_refined_raft_net_invariant_do_leader' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_do_leader', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_do_leader; eauto.
    - eapply commit_invariant_do_leader; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_do_leader; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma everything_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_do_generic_server', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_do_generic_server; eauto.
    - eapply commit_invariant_do_generic_server; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_do_generic_server; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Lemma directly_committed_state_same :
    forall net net' e,
      (forall h, nwState net' h = nwState net h) ->
      directly_committed net e ->
      directly_committed net' e.
  Proof.
    unfold directly_committed.
    intuition.
    break_exists_exists.
    intuition.
    find_higher_order_rewrite. auto.
  Qed.

  Lemma lifted_committed_state_same :
    forall (net net' : ghost_log_network) e t,
      (forall h, nwState net' h = nwState net h) ->
      lifted_committed net e t ->
      lifted_committed net' e t.
  Proof.
    intuition.
    destruct net, net'.
    simpl in *.
    eapply lifted_committed_ext'; eauto.
  Qed.

  Lemma exists_in_mgv_deghost_packet :
    forall (p : packet (params := raft_refined_multi_params)) (net : ghost_log_network),
      In p (nwPackets (mgv_deghost net)) ->
      exists q,
        In q (nwPackets net) /\
        pDst q = pDst p /\
        pSrc q = pSrc p /\
        snd (pBody q) = pBody p.
  Proof.
    unfold mgv_deghost.
    simpl.
    intros.
    do_in_map.
    subst. simpl.
    eauto.
  Qed.

  Lemma state_machine_safety'_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset
      (fun net : ghost_log_network =>  state_machine_safety' (mgv_deghost net)).
  Proof.
    unfold msg_refined_raft_net_invariant_state_same_packet_subset, state_machine_safety'.
    intuition.
    - unfold state_machine_safety_host' in *. intuition.
      repeat find_apply_lem_hyp committed_lifted_committed.
      eauto 6 using lifted_committed_committed, lifted_committed_state_same.
    - unfold state_machine_safety_nw' in *. intuition.

      find_apply_lem_hyp exists_in_mgv_deghost_packet. break_exists. break_and.
      find_apply_hyp_hyp.
      find_apply_lem_hyp in_mgv_ghost_packet.
      match goal with
      | [ H : context [ pBody ] |- _ ] =>
        eapply H; eauto
      end.
      + rewrite pBody_mgv_deghost_packet. repeat find_rewrite. eauto.
      + apply lifted_committed_committed.
        eapply lifted_committed_state_same; eauto using committed_lifted_committed.
  Qed.

  Lemma CRC_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset
      (fun net : ghost_log_network => commit_recorded_committed (mgv_deghost net)).
  Proof.
    unfold msg_refined_raft_net_invariant_state_same_packet_subset, commit_recorded_committed,
           commit_recorded, committed, directly_committed.
    intros.
    specialize (H1 h e).
    repeat find_rewrite_lem deghost_spec.
    repeat find_rewrite_lem msg_deghost_spec'.
    repeat find_higher_order_rewrite.
    find_apply_hyp_hyp.
    break_exists_exists.
    repeat find_rewrite_lem msg_deghost_spec'.
    repeat rewrite msg_deghost_spec'.
    repeat find_higher_order_rewrite.
    intuition.
    break_exists_exists.
    intuition.
    find_apply_hyp_hyp.
    repeat find_rewrite_lem msg_deghost_spec'.
    repeat rewrite msg_deghost_spec'.
    repeat find_higher_order_rewrite.
    auto.
  Qed.

  Lemma everything_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_state_same_packet_subset', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_state_same_packet_subset; eauto.
    - eapply commit_invariant_state_same_packet_subset; eauto.
    - apply state_machine_safety_deghost.
      + eapply CRC_state_same_packet_subset; eauto.
        apply commit_invariant_lower_commit_recorded_committed; auto.

      + eapply state_machine_safety'_state_same_packet_subset; eauto.
        auto using state_machine_safety'_invariant, msg_simulation_1.
  Qed.

  Require Import FunctionalExtensionality.

  Lemma everything_reboot :
    msg_refined_raft_net_invariant_reboot' everything.
  Proof.
    unfold msg_refined_raft_net_invariant_reboot', everything.
    intuition.
    - eapply lifted_maxIndex_sanity_reboot; eauto.
    - eapply commit_invariant_reboot; eauto.
    - apply state_machine_safety_deghost.
      + apply commit_invariant_lower_commit_recorded_committed. auto.
        eapply commit_invariant_reboot; eauto.
      + apply state_machine_safety'_invariant. auto using msg_simulation_1.
  Qed.

  Theorem everything_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      everything net.
  Proof.
    intros.
    apply msg_refined_raft_net_invariant'; auto.
    - apply everything_init.
    - apply everything_client_request.
    - apply everything_timeout.
    - apply everything_append_entries.
    - apply everything_append_entries_reply.
    - apply everything_request_vote.
    - apply everything_request_vote_reply.
    - apply everything_do_leader.
    - apply everything_do_generic_server.
    - apply everything_state_same_packet_subset.
    - apply everything_reboot.
  Qed.

  Theorem state_machine_safety_invariant :
    forall net,
      raft_intermediate_reachable net ->
      state_machine_safety net.
  Proof.
    intros.
    apply lower_prop; intros; auto.
    apply msg_lower_prop with (P := fun net => _ (deghost net)); intros; auto.
    find_apply_lem_hyp everything_invariant.
    unfold everything in *. intuition.
  Qed.

  Theorem maxIndex_sanity_invariant :
    forall net,
      raft_intermediate_reachable net ->
      maxIndex_sanity net.
  Proof.
    intros.
    apply lower_prop; intros; eauto.
    apply msg_lower_prop with (P := fun net => _ (deghost net)); intros; auto.
    find_apply_lem_hyp everything_invariant.
    unfold everything in *. intuition.
    auto using maxIndex_sanity_lower.
  Qed.

  Theorem commit_recorded_committed_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      commit_recorded_committed net.
  Proof.
    intros.
    apply msg_lower_prop; intros; auto.
    find_copy_apply_lem_hyp everything_invariant.
    unfold everything in *.
    intuition.
    auto using commit_invariant_lower_commit_recorded_committed.
  Qed.

  Instance smsi : state_machine_safety_interface.
  Proof.
    split.
    exact state_machine_safety_invariant.
  Qed.

  Instance misi : max_index_sanity_interface.
  Proof.
    split.
    exact maxIndex_sanity_invariant.
  Qed.

  Instance crci : commit_recorded_committed_interface.
  Proof.
    split.
    intros.
    find_apply_lem_hyp commit_recorded_committed_invariant.
    unfold commit_invariant, commit_recorded_committed, commit_recorded in *.
    intros.
    find_rewrite_lem (deghost_spec net h).
    intuition;
    repeat match goal with
             | [ H : forall _, _, h : entry |- _ ] => specialize (H h)
             | [ H : forall _, _, h : Net.name |- _ ] => specialize (H h)
           end;
    repeat find_rewrite_lem deghost_spec; auto.
  Qed.
End StateMachineSafetyProof.
