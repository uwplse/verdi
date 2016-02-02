Require Import List.
Import ListNotations.
Require Import Omega.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import GhostSimulations.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonDefinitions.
Require Import CommonTheorems.

Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LogMatchingInterface.
Require Import LeaderLogsTermSanityInterface.
Require Import LeaderLogsSortedInterface.
Require Import SortedInterface.
Require Import LeaderLogsSublogInterface.
Require Import LeaderLogsContiguousInterface.
Require Import TermsAndIndicesFromOneInterface.

Require Import LeaderLogsLogMatchingInterface.

Section LeaderLogsLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lmi : log_matching_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {llsi : leaderLogs_sorted_interface}.
  Context {si : sorted_interface}.
  Context {llsli : leaderLogs_sublog_interface}.
  Context {llci : leaderLogs_contiguous_interface}.
  Context {taifoi : terms_and_indices_from_one_interface}.

  Definition leaderLogs_entries_match_nw (net : network) : Prop :=
    forall h llt ll p t src pli plt es ci,
      In (llt, ll) (leaderLogs (fst (nwState net h))) ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t src pli plt es ci ->
      (forall e1 e2,
         eIndex e1 = eIndex e2 ->
         eTerm e1 = eTerm e2 ->
         In e1 es ->
         In e2 ll ->
         (forall e3,
            eIndex e3 <= eIndex e1 ->
            In e3 es ->
            In e3 ll) /\
         (pli <> 0 ->
          exists e4,
            eIndex e4 = pli /\
            eTerm e4 = plt /\
            In e4 ll)).

  Definition leaderLogs_entries_match (net : network) : Prop :=
    leaderLogs_entries_match_host net /\
    leaderLogs_entries_match_nw net.

  Lemma leaderLogs_entries_match_init :
    refined_raft_net_invariant_init leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_init, leaderLogs_entries_match,
           leaderLogs_entries_match_host, leaderLogs_entries_match_nw.
    simpl.
    intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma entries_match_cons_gt_maxTerm :
    forall x xs ys,
      sorted xs ->
      sorted ys ->
      eIndex x > maxIndex xs ->
      eTerm x > maxTerm ys ->
      entries_match xs ys ->
      entries_match (x :: xs) ys.
  Proof.
    unfold entries_match.
    intuition; simpl in *; intuition; subst; subst;
    try match goal with
        | [ H : In _ _ |- _ ] => apply maxTerm_is_max in H; [| solve[auto]]; omega
        | [ H : In _ _ |- _ ] => apply maxIndex_is_max in H; [| solve[auto]]; omega
      end.
    - match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
    - right. match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
  Qed.

  Lemma entries_match_cons_sublog :
    forall x xs ys,
      sorted xs ->
      sorted ys ->
      eIndex x > maxIndex xs ->
      entries_match xs ys ->
      (forall y, In y ys -> eTerm x = eTerm y -> In y xs) ->
      entries_match (x :: xs) ys.
  Proof.
    unfold entries_match.
    intuition; simpl in *; intuition; subst; subst;
    try solve [
         exfalso; try find_apply_hyp_hyp;
          match goal with
            | [ H : In _ _ |- _ ] => apply maxIndex_is_max in H; [| solve[auto]]; omega
          end].
    - match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
    - right. match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
  Qed.

  Lemma entries_match_nil :
    forall l,
      entries_match l [].
  Proof.
    red.
    simpl.
    intuition.
  Qed.

  Lemma lifted_logs_sorted_nw :
    forall net p t n plt plti es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n plt plti es ci ->
      sorted es.
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    find_insterU. conclude_using eauto.
    unfold logs_sorted in *. break_and.
    unfold logs_sorted_nw in *.
    eapply H3.
    - unfold deghost. simpl.
      apply in_map_iff. eauto.
    - simpl. eauto.
  Qed.

  Lemma lifted_logs_sorted_host :
    forall net h ,
      refined_raft_intermediate_reachable net ->
      sorted (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    find_insterU. conclude_using eauto.
    unfold logs_sorted in *. break_and.
    unfold logs_sorted_host in *.
    find_insterU.
    find_rewrite_lem deghost_spec.
    eauto.
  Qed.

  Lemma leaderLogs_entries_match_nw_packet_set :
    forall net net',
      leaderLogs_entries_match_nw net ->
      (forall p, In p (nwPackets net') ->
                 is_append_entries (pBody p) ->
                 In p (nwPackets net)) ->
      (forall h, leaderLogs (fst (nwState net' h)) = leaderLogs (fst (nwState net h))) ->
      leaderLogs_entries_match_nw net'.
  Proof.
    unfold leaderLogs_entries_match_nw.
    intros.
    eapply_prop_hyp In nwPackets; [|eauto 10].
    match goal with
      | [ H : _ |- _ ] =>
        solve [eapply H; eauto;
               repeat find_higher_order_rewrite;
               eauto]
    end.
  Qed.

  Lemma leaderLogs_entries_match_host_state_same :
    forall net net',
      leaderLogs_entries_match_host net ->
      (forall h, leaderLogs (fst (nwState net' h)) = leaderLogs (fst (nwState net h))) ->
      (forall h, log (snd (nwState net' h)) = log (snd (nwState net h))) ->
      leaderLogs_entries_match_host net'.
  Proof.
    unfold leaderLogs_entries_match_host.
    intuition.
    repeat find_higher_order_rewrite. eauto.
  Qed.

  Lemma handleClientRequest_no_send :
    forall h st client id c out st' ms,
      handleClientRequest h st client id c = (out, st', ms) ->
      ms = [].
  Proof.
    unfold handleClientRequest.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma leaderLogs_entries_match_client_request :
    refined_raft_net_invariant_client_request leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_client_request, leaderLogs_entries_match.
    intros.
    split.
    - { unfold leaderLogs_entries_match_host.
        simpl. intuition. subst. repeat find_higher_order_rewrite.
        repeat update_destruct.
        - find_rewrite_lem update_elections_data_client_request_leaderLogs.
          destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
          + eauto.
          + destruct ll.
            * apply entries_match_nil.
            * { apply entries_match_cons_gt_maxTerm; eauto.
                - eauto using lifted_logs_sorted_host.
                - eapply leaderLogs_sorted_invariant; eauto.
                - omega.
                - find_copy_apply_lem_hyp leaderLogs_currentTerm_invariant; auto.
                  find_copy_apply_lem_hyp leaderLogs_term_sanity_invariant.
                  unfold leaderLogs_term_sanity in *.
                  eapply_prop_hyp In In; simpl; eauto. repeat find_rewrite.
                  simpl in *. omega.
              }
        - find_rewrite_lem update_elections_data_client_request_leaderLogs.
          eauto.
        - destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
          + eauto.
          + apply entries_match_cons_sublog; eauto.
            * eauto using lifted_logs_sorted_host.
            * eapply leaderLogs_sorted_invariant; eauto.
            * omega.
            * intros.
              eapply leaderLogs_sublog_invariant; eauto.
              simpl in *. congruence.
        - eauto.
      }
    - eapply leaderLogs_entries_match_nw_packet_set with (net:=net); intuition.
      + find_apply_hyp_hyp. intuition eauto.
        erewrite handleClientRequest_no_send with (ms := l) in * by eauto.
        simpl in *. intuition.
      + simpl. subst. find_higher_order_rewrite.
        rewrite update_fun_comm. simpl.
        rewrite update_fun_comm. simpl.
        rewrite update_elections_data_client_request_leaderLogs.
        now rewrite update_nop_ext' by auto.
  Qed.

  Lemma leaderLogs_entries_match_timeout :
    refined_raft_net_invariant_timeout leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_timeout, leaderLogs_entries_match.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto;
      simpl; intros; subst; find_higher_order_rewrite;
      repeat update_destruct; rewrite_update; auto;
      try rewrite update_elections_data_timeout_leaderLogs;
      try erewrite handleTimeout_log_same by eauto; eauto.
    - eapply leaderLogs_entries_match_nw_packet_set with (net:=net); intuition.
      + simpl in *. find_apply_hyp_hyp.  intuition.
        do_in_map. subst. simpl in *.
        exfalso. eapply handleTimeout_not_is_append_entries; eauto 10.
      + simpl. repeat find_higher_order_rewrite.
        rewrite update_fun_comm. simpl.
        rewrite update_fun_comm. simpl.
        rewrite update_elections_data_timeout_leaderLogs.
        rewrite update_nop_ext'; auto.
  Qed.

  Lemma lifted_log_matching :
    forall net,
      refined_raft_intermediate_reachable net ->
      log_matching (deghost net).
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    find_insterU. conclude_using eauto.
    auto.
  Qed.

  Lemma lifted_log_matching_host :
    forall net,
      refined_raft_intermediate_reachable net ->
      (forall h h',
         entries_match (log (snd (nwState net h))) (log (snd (nwState net h')))) /\
      (forall h i,
         1 <= i <= maxIndex (log (snd (nwState net h))) ->
         exists e, eIndex e = i /\ In e (log (snd (nwState net h)))) /\
      (forall h e,
         In e (log (snd (nwState net h))) -> eIndex e > 0).
  Proof.
    intros.
    find_apply_lem_hyp lifted_log_matching.
    unfold log_matching, log_matching_hosts in *.
    intuition; repeat rewrite <- deghost_spec with (net0 := net).
    - auto.
    - match goal with
        | [ H : _ |- _ ] => solve [apply H; rewrite deghost_spec; auto]
      end.
    - match goal with
        | [ H : _ |- _ ] => solve [eapply H; rewrite deghost_spec; eauto]
      end.
  Qed.

  Lemma lifted_log_matching_nw :
    forall net,
      refined_raft_intermediate_reachable net ->
      forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
        In p (nwPackets net) ->
        pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
        (forall h e1 e2,
           In e1 entries ->
           In e2 (log (snd (nwState net h))) ->
           eIndex e1 = eIndex e2 ->
           eTerm e1 = eTerm e2 ->
           (forall e3,
              eIndex e3 <= eIndex e1 ->
              In e3 entries ->
              In e3 (log (snd (nwState net h)))) /\
           (prevLogIndex <> 0 ->
            exists e4,
              eIndex e4 = prevLogIndex /\
              eTerm e4 = prevLogTerm /\
              In e4 (log (snd (nwState net h))))) /\
        (forall i,
           prevLogIndex < i <= maxIndex entries ->
           exists e,
             eIndex e = i /\
             In e entries) /\
        (forall e,
           In e entries ->
           prevLogIndex < eIndex e).
  Proof.
    intros.
    find_apply_lem_hyp lifted_log_matching.
    unfold log_matching, log_matching_nw in *.
    break_and.
    match goal with
      | [ H : forall _ : packet , _ |- _ ] =>
        do 7 insterU H;
          conclude H ltac:(unfold deghost; simpl; eapply in_map_iff; eexists; eauto);
          conclude H ltac:(simpl; eauto)
    end.
    intuition.
    - rewrite <- deghost_spec with (net0 := net).
      eapply H3 with (e1:=e1)(e2:=e2); eauto.
      rewrite deghost_spec.  auto.
    - rewrite <- deghost_spec with (net0 := net).
      eapply H3 with (e1:=e1)(e2:=e2); eauto.
      rewrite deghost_spec.  auto.
  Qed.

  Ltac use_log_matching_nw :=
    pose proof (lifted_log_matching_nw _ ltac:(eauto));
    match goal with
      | [ H : _  |- _ ] =>
        eapply H; [|eauto];
        repeat find_rewrite; intuition
    end.

  Lemma handleAppendEntries_doesn't_send_AE :
    forall n st t i l t' l' l'' st' m,
      handleAppendEntries n st t i l t' l' l'' = (st', m) ->
      ~ is_append_entries m.
  Proof.
    unfold handleAppendEntries.
    intros.
    repeat break_match; find_inversion; intro; break_exists; discriminate.
  Qed.

  Lemma leaderLogs_entries_match_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_append_entries, leaderLogs_entries_match.
    intuition.
    - unfold leaderLogs_entries_match_host in *. intros.
      {
        intros. simpl in *. repeat find_higher_order_rewrite.
        find_rewrite_lem update_fun_comm. simpl in *.
        find_rewrite_lem update_fun_comm.
        find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
        find_erewrite_lem update_nop_ext'.
        update_destruct; rewrite_update;
        try rewrite update_elections_data_appendEntries_leaderLogs in *; eauto.
        destruct (log d) using (handleAppendEntries_log_ind ltac:(eauto)); eauto.
        + subst. eapply entries_match_scratch with (plt0 := plt).
          * eauto using lifted_logs_sorted_nw.
          * apply sorted_uniqueIndices.
            eapply leaderLogs_sorted_invariant; eauto.
          * eapply_prop leaderLogs_entries_match_nw; eauto.
          * use_log_matching_nw.
          * use_log_matching_nw.
          * match goal with
              | [ H : In _ (leaderLogs _) |- _ ] =>
                eapply terms_and_indices_from_one_invariant in H; [|solve[auto]]
            end.
            unfold terms_and_indices_from_one in *. intros.
            find_apply_hyp_hyp. intuition.
        + eapply entries_match_append; eauto.
          * eauto using lifted_logs_sorted_host.
          * eapply leaderLogs_sorted_invariant; eauto.
          * eauto using lifted_logs_sorted_nw.
          * use_log_matching_nw.
          * use_log_matching_nw.
          * eapply findAtIndex_intro; eauto using lifted_logs_sorted_host, sorted_uniqueIndices.
      }
    - (* nw *)
      unfold leaderLogs_entries_match_nw in *.
      intros. simpl in *. repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      find_rewrite_lem update_fun_comm.
      find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
      find_erewrite_lem update_nop_ext'.
      find_apply_hyp_hyp. break_or_hyp.
      + intuition; match goal with
            | [ H : _ |- _ ] => solve [eapply H with (p0 := p0); eauto with *]
          end.
      + simpl in *.
        find_copy_apply_lem_hyp handleAppendEntries_doesn't_send_AE.
        exfalso. eauto 10.
  Qed.

  Lemma leaderLogs_entries_match_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, leaderLogs_entries_match.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros;
      repeat find_higher_order_rewrite; update_destruct; rewrite_update; auto.
      erewrite handleAppendEntriesReply_same_log by eauto. auto.
    - eapply leaderLogs_entries_match_nw_packet_set; eauto; simpl.
      + intros. find_apply_hyp_hyp. repeat find_rewrite. intuition; [eauto with *|].
        find_apply_lem_hyp handleAppendEntriesReply_packets. subst. simpl in *. intuition.
      + intros. repeat find_higher_order_rewrite; update_destruct; rewrite_update; auto; find_rewrite; auto.
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

  Lemma leaderLogs_entries_match_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_request_vote, leaderLogs_entries_match.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros;
      repeat find_higher_order_rewrite; update_destruct; rewrite_update; auto.
      + now rewrite leaderLogs_update_elections_data_requestVote.
      + erewrite handleRequestVote_log; eauto.
    - eapply leaderLogs_entries_match_nw_packet_set; eauto; simpl.
      + intros. find_apply_hyp_hyp. repeat find_rewrite. intuition; [eauto with *|].
        find_apply_lem_hyp handleRequestVote_packets. subst. simpl in *. intuition.
      + intros. repeat find_higher_order_rewrite; update_destruct; rewrite_update; auto.
        now rewrite leaderLogs_update_elections_data_requestVote.
  Qed.

  Lemma leaderLogs_entries_match_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, leaderLogs_entries_match.
    intuition.
    - unfold leaderLogs_entries_match_host in *.
      intros. simpl in *. subst.
      repeat find_higher_order_rewrite.
      rewrite update_fun_comm. simpl.
      rewrite update_fun_comm. simpl.
      rewrite update_nop_ext' by now rewrite handleRequestVoteReply_same_log.
      find_rewrite_lem update_fun_comm. simpl in *.
      update_destruct; rewrite_update; eauto.
      find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
      intuition eauto.
      subst.
      rewrite handleRequestVoteReply_same_log.
      apply lifted_log_matching_host. auto.
    - unfold leaderLogs_entries_match_nw in *.
      intros. simpl in *. subst.
      repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      find_rewrite_lem update_fun_comm.
      update_destruct; rewrite_update.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
        break_or_hyp.
        * repeat find_reverse_rewrite. eauto.
        * break_and. subst.
          rewrite handleRequestVoteReply_same_log.
          find_rewrite_lem handleRequestVoteReply_same_log.
          pose proof (lifted_log_matching_nw _ ltac:(eauto)).
          repeat find_reverse_rewrite.
          match goal with
            | [ H : _, pkt : packet  |- _ ] =>
              solve [eapply H with (p := pkt); eauto]
          end.
      + repeat find_reverse_rewrite. eauto.
  Qed.

  Lemma doLeader_messages :
    forall st h os st' ms,
      doLeader st h = (os, st', ms) ->
      ms = [] \/
      ms = map (replicaMessage st' h)
               (filter (fun h' : name => if name_eq_dec h h' then false else true)
                       nodes).
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma leaderLogs_entries_match_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_do_leader, leaderLogs_entries_match.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros;
      find_higher_order_rewrite; update_destruct; rewrite_update; auto.
      + find_rewrite. auto.
      + erewrite doLeader_same_log by eauto. find_rewrite. auto.
    - unfold leaderLogs_entries_match_nw in *. intros. simpl in *.
      repeat find_higher_order_rewrite.
      find_rewrite_lem update_fun_comm. simpl in *.
      match goal with
        | [ H : _ |- _ ] =>
          rewrite update_nop_ext' in H by (find_rewrite; auto)
      end.
      find_apply_hyp_hyp. break_or_hyp.
      + find_reverse_rewrite. eauto.
      + do_in_map. subst. simpl in *.
        find_copy_apply_lem_hyp doLeader_messages.
        break_or_hyp.
        * simpl in *. intuition.
        * do_in_map. find_apply_lem_hyp filter_In.
          break_and. break_if; try discriminate.
          unfold replicaMessage in *. subst. simpl in *. find_inversion.
          { intuition.
            - repeat find_erewrite_lem doLeader_same_log.
              eapply_prop leaderLogs_entries_match_host; eauto.
              + match goal with
                  | [ H : _ |- _ ] => rewrite H
                end. simpl.
                eauto using findGtIndex_in.
              + auto with *.
              + find_rewrite. simpl. eauto using findGtIndex_in.
            - find_copy_apply_lem_hyp leaderLogs_contiguous_invariant; auto.
              unfold contiguous_range_exact_lo in *. break_and.
              match goal with
                | [ H : forall _, _ < _ <= _ -> _ |- context [eIndex _ = ?x]] =>
                  remember (x) as index;
                  specialize (H index); forward H
              end.
              + intuition; auto using neq_0_lt.
                find_apply_lem_hyp findGtIndex_necessary. break_and.
                eapply le_trans.
                * apply lt_le_weak. eauto.
                * repeat find_rewrite. eapply maxIndex_is_max; auto.
                  eapply leaderLogs_sorted_invariant; eauto.
              + concludes. break_exists_exists. intuition.
                match goal with
                  | [ H : context [leaderLogs_entries_match_host],
                     H' : context [leaderLogs] |- _ ] =>
                    eapply H with (h := src)(e := e1)(e' := e2)(e'' := x) in H'; auto
                end.
                * pose proof lifted_logs_sorted_host net src ltac:(auto).
                  repeat find_rewrite. simpl in *.
                  repeat find_erewrite_lem doLeader_same_log.
                  erewrite doLeader_same_log by eauto.
                  erewrite findAtIndex_intro; eauto using sorted_uniqueIndices.
                * find_apply_lem_hyp findGtIndex_necessary. break_and.
                  repeat find_erewrite_lem doLeader_same_log.
                  repeat find_rewrite. simpl in *.
                  auto.
                * find_apply_lem_hyp findGtIndex_necessary. break_and.
                  omega.
          }
  Qed.

  Lemma doGenericServer_packets :
    forall h st os st' ps,
      doGenericServer h st = (os, st', ps) ->
      ps = [].
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Lemma leaderLogs_entries_match_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, leaderLogs_entries_match.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros;
      find_higher_order_rewrite; update_destruct; rewrite_update; auto.
      + find_rewrite. auto.
      + erewrite doGenericServer_log by eauto. find_rewrite. auto.
    - eapply leaderLogs_entries_match_nw_packet_set; eauto; simpl.
      + intros. find_apply_hyp_hyp. intuition.
        find_apply_lem_hyp doGenericServer_packets. subst. simpl in *. intuition.
      + intros. find_higher_order_rewrite; update_destruct; rewrite_update; auto; find_rewrite; auto.
  Qed.

  Lemma leaderLogs_entries_match_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, leaderLogs_entries_match.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto; intros; find_higher_order_rewrite; auto.
    - eapply leaderLogs_entries_match_nw_packet_set; eauto; intros; find_higher_order_rewrite; auto.
  Qed.

  Lemma leaderLogs_entries_match_reboot :
    refined_raft_net_invariant_reboot leaderLogs_entries_match.
  Proof.
    unfold refined_raft_net_invariant_reboot, leaderLogs_entries_match, reboot.
    intuition.
    - eapply leaderLogs_entries_match_host_state_same; eauto; intros; find_higher_order_rewrite;
      update_destruct; rewrite_update; auto; find_rewrite; auto.
    - eapply leaderLogs_entries_match_nw_packet_set; eauto; try find_rewrite; intuition.
      find_higher_order_rewrite; update_destruct; rewrite_update; try find_rewrite; auto.
  Qed.

  Lemma leaderLogs_entries_match_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_entries_match net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_entries_match_init.
    - apply leaderLogs_entries_match_client_request.
    - apply leaderLogs_entries_match_timeout.
    - apply leaderLogs_entries_match_append_entries.
    - apply leaderLogs_entries_match_append_entries_reply.
    - apply leaderLogs_entries_match_request_vote.
    - apply leaderLogs_entries_match_request_vote_reply.
    - apply leaderLogs_entries_match_do_leader.
    - apply leaderLogs_entries_match_do_generic_server.
    - apply leaderLogs_entries_match_state_same_packet_subset.
    - apply leaderLogs_entries_match_reboot.
  Qed.

  Instance lllmi : leaderLogs_entries_match_interface : Prop.
  Proof.
    split.
    apply leaderLogs_entries_match_invariant.
  Qed.
End LeaderLogsLogMatching.
