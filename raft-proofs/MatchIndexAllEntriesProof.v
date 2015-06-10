Require Import List.
Require Import Omega.

Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.
Require Import RefinementCommonTheorems.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import NoAppendEntriesToLeaderInterface.
Require Import NoAppendEntriesToSelfInterface.
Require Import TermsAndIndicesFromOneLogInterface.
Require Import RefinedLogMatchingLemmasInterface.
Require Import LogAllEntriesInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import LeaderSublogInterface.
Require Import LeadersHaveLeaderLogsStrongInterface.
Require Import OneLeaderLogPerTermInterface.

Require Import MatchIndexAllEntriesInterface.

Section MatchIndexAllEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Context {naetli : no_append_entries_to_leader_interface}.
  Context {naetsi : no_append_entries_to_self_interface}.
  Context {taifoli : terms_and_indices_from_one_log_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {laei : log_all_entries_interface}.
  Context {aelli : append_entries_leaderLogs_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.

  Definition match_index_all_entries_nw (net : network) : Prop :=
    forall p t es e,
      In p (nwPackets net) ->
      pBody p = AppendEntriesReply t es true ->
      currentTerm (snd (nwState net (pDst p))) = t ->
      In e (log (snd (nwState net (pDst p)))) ->
      eTerm e = t ->
      eIndex e <= maxIndex es ->
      type (snd (nwState net (pDst p))) = Leader ->
      In (t, e) (allEntries (fst (nwState net (pSrc p)))).

  Definition match_index_all_entries_inv (net : network) : Prop :=
    match_index_all_entries net /\ match_index_all_entries_nw net.

  Lemma match_index_all_entries_init :
    refined_raft_net_invariant_init match_index_all_entries_inv.
  Proof.
    unfold refined_raft_net_invariant_init,
           match_index_all_entries_inv,
           match_index_all_entries_nw,
           match_index_all_entries.
    simpl. intros.
    intuition.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ H : context [ update _ ?x _ ?y ] |- _ ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
      | [ |- context [ update _ ?x _ ?y ] ] =>
        destruct (name_eq_dec x y); subst; rewrite_update; simpl in *
    end.

  Lemma match_index_all_entries_client_request :
    refined_raft_net_invariant_client_request match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_timeout :
    refined_raft_net_invariant_timeout match_index_all_entries_inv.
  Admitted.

  Lemma handleAppendEntries_post_leader_nop :
    forall h st t n pli plt es ci st' m,
      currentTerm st <> t ->
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      type st' = Leader ->
      st' = st.
  Proof.
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; auto; try discriminate.
  Qed.

  Lemma handleAppendEntries_leader_was_leader :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      type st' = Leader ->
      type st = Leader.
  Proof.
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; auto; try discriminate.
  Qed.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof.
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Lemma pDst_deghost_packet :
    forall p : packet (params := raft_refined_multi_params),
      pDst (deghost_packet p) = pDst p.
  Proof.
    unfold deghost_packet. auto.
  Qed.

  Lemma lifted_no_AE_to_leader :
    forall net p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (snd (nwState net (pDst p))) = Leader ->
      currentTerm (snd (nwState net (pDst p))) = t ->
      False.
  Proof.
    intros.
    pose proof (lift_prop _ no_append_entries_to_leader_invariant _ $(eauto)$).
    unfold no_append_entries_to_leader in *.
    find_apply_lem_hyp ghost_packet.
    match goal with
    | [ H : forall _ _ _ , _, H' : In _ _ |- _ ] => eapply H in H'; eauto
    end;
    rewrite deghost_spec;
    rewrite pDst_deghost_packet; auto.
  Qed.

  Lemma lifted_no_AE_to_self :
    forall net p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      pDst p = pSrc p ->
      False.
  Proof.
    intros.
    pose proof (lift_prop _ no_append_entries_to_self_invariant _ $(eauto)$).
    unfold no_append_entries_to_self in *.
    find_apply_lem_hyp ghost_packet.
    match goal with
    | [ H : forall _ _ _ , _, H' : In _ _ |- _ ] => eapply H in H'; eauto
    end.
  Qed.

  Lemma handleAppendEntries_message :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      exists res, m = AppendEntriesReply (currentTerm st') es res.
  Proof.
    unfold handleAppendEntries, advanceCurrentTerm.
    intros. repeat break_match; repeat find_inversion; simpl in *; repeat do_bool; eauto;
            eexists; f_equal; eauto using NPeano.Nat.le_antisymm.
  Qed.

  Lemma not_empty_true_elim :
    forall A (l : list A),
      not_empty l = true -> l <> nil.
  Proof.
    unfold not_empty.
    intros. break_match; congruence.
  Qed.

  Lemma not_empty_false_elim :
    forall A (l : list A),
      not_empty l = false -> l = nil.
  Proof.
    unfold not_empty.
    intros. break_match; congruence.
  Qed.

  Lemma handleAppendEntries_success_allEntries :
    forall h st t n pli plt es ci st' t',
      handleAppendEntries h st t n pli plt es ci = (st', AppendEntriesReply t' es true) ->
      es <> nil ->
      (forall e e' e'',
          In e es ->
          In e' (log st) ->
          eIndex e = eIndex e' ->
          eTerm e = eTerm e' ->
          In e'' es ->
          eIndex e'' <= eIndex e ->
          In e'' (log st)) ->
      sorted (log st) ->
      exists e, In e (log st') /\ In e es /\
                eIndex e = maxIndex es /\
                eTerm e = maxTerm es.
  Proof.
    unfold handleAppendEntries, haveNewEntries.
    intros.
    break_if; try find_inversion.
    break_if.
    - break_if; find_inversion; simpl;
      repeat (do_bool; repeat break_and).
      + find_apply_lem_hyp not_empty_true_elim.
        pose proof maxIndex_non_empty es $(auto)$.
        break_exists_exists. intuition.
      + break_or_hyp.
        * find_apply_lem_hyp not_empty_false_elim. congruence.
        * break_match; try discriminate.
          do_bool. rewrite advanceCurrentTerm_log.
          find_apply_lem_hyp findAtIndex_elim. break_and.
          pose proof maxIndex_non_empty es $(auto)$.
          break_exists_name e'. break_and.
          match goal with
          | [ H : forall _ _ _, In _ _ -> _ |- _ ] =>
            specialize (H e' e e')
          end.
          repeat find_rewrite. repeat concludes. intuition.
          assert (e = e').
          { eapply uniqueIndices_elim_eq; eauto.
            auto using sorted_uniqueIndices.
          }
          subst. eauto.
    - break_match; try find_inversion.
      break_if; try find_inversion.
      break_if; find_inversion; simpl;
      repeat (do_bool; repeat break_and).
      + find_apply_lem_hyp not_empty_true_elim.
        pose proof maxIndex_non_empty es $(auto)$.
        break_exists_exists. intuition.
      + break_or_hyp.
        * find_apply_lem_hyp not_empty_false_elim. congruence.
        * break_match; try discriminate.
          do_bool. rewrite advanceCurrentTerm_log.
          find_apply_lem_hyp findAtIndex_elim. break_and.
          pose proof maxIndex_non_empty es $(auto)$.
          break_exists_name e'. break_and.
          match goal with
          | [ H : forall _ _ _, In _ _ -> _ |- _ ] =>
            specialize (H e' e0 e')
          end.
          repeat find_rewrite. repeat concludes. intuition.
          assert (e0 = e').
          { eapply uniqueIndices_elim_eq; eauto.
            auto using sorted_uniqueIndices.
          }
          subst. eauto.
  Qed.

  Lemma handleAppendEntries_success_term :
    forall h st t n pli plt es ci st' t',
      handleAppendEntries h st t n pli plt es ci = (st', AppendEntriesReply t' es true) ->
      currentTerm st' = t.
  Proof.
    unfold handleAppendEntries, advanceCurrentTerm.
    intros. repeat break_match; repeat find_inversion; simpl; auto; repeat do_bool;
    eauto using Nat.le_antisymm.
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

  Lemma maxIndex_gt_0_nonempty :
    forall es,
      0 < maxIndex es ->
      es <> nil.
  Proof.
    intros.
    destruct es; simpl in *.
    - omega.
    - congruence.
  Qed.

  Lemma lifted_leader_sublog_nw :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (snd (nwState net h)) = Leader ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof.
    intros.
    pose proof (lift_prop _ leader_sublog_invariant_invariant _ $(eauto)$) as Hinv.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant in *.
    destruct Hinv as [Hhost Hnw].
    find_apply_lem_hyp ghost_packet.
    eapply_prop_hyp In In; eauto; try find_rewrite_lem deghost_spec; try rewrite deghost_spec; eauto.
  Qed.

  Lemma appendEntries_sublog :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Leader ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof.
    intros.
    find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
    break_exists. break_and.
    subst es.
    find_apply_lem_hyp in_app_or. break_or_hyp.
    - find_copy_apply_hyp_hyp.
      eapply lifted_leader_sublog_nw; eauto. intuition.
    - find_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; auto.
      break_exists.  break_and.
      pose proof one_leaderLog_per_term_invariant _ $(eauto)$ h x _ x3 x0 $(eauto)$ $(eauto)$.
      break_and. subst.
      find_rewrite. eauto using Prefix_In with *.
  Qed.

  Lemma match_index_all_entries_append_entries :
    refined_raft_net_invariant_append_entries' match_index_all_entries_inv.
  Proof.
    unfold refined_raft_net_invariant_append_entries', match_index_all_entries_inv.
    simpl. intros. break_and.
    split.
    - admit.
    - unfold match_index_all_entries_nw. simpl.  intros.
      find_apply_hyp_hyp. break_or_hyp.
      + unfold match_index_all_entries_nw in *.
        repeat find_higher_order_rewrite.
        update_destruct.
        * assert (currentTerm (snd (nwState net (pDst p))) <> t).
          { intro.
            match goal with
            | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] =>
              eapply lifted_no_AE_to_leader with (net := net) in H; eauto
            end.
            eapply handleAppendEntries_leader_was_leader; eauto.
          }
          match goal with
          | [ H : context [handleAppendEntries] |- _ ] =>
            apply handleAppendEntries_post_leader_nop in H; auto
          end.
          subst.
          match goal with
          | [ H : In _ (_ ++ _), H' : forall _ _ _ _, In _ _ -> _ |- _ ] =>
            eapply in_middle_insert in H; eapply H' in H; eauto; try congruence
          end.
          { update_destruct.
            - apply update_elections_data_appendEntries_preserves_allEntries.
              repeat find_rewrite. auto.
            - auto.
          }
        * match goal with
          | [ H : forall _ _ _ _, In _ _ -> _, H' : pBody _ = AppendEntriesReply _ _ _ |- _ ] =>
            eapply H in H'; eauto
          end.
          { update_destruct.
            - apply update_elections_data_appendEntries_preserves_allEntries.
              repeat find_rewrite. auto.
            - auto.
          }
      + simpl in *.
        find_copy_apply_lem_hyp handleAppendEntries_message. break_exists.
        subst. find_inversion.
        repeat find_higher_order_rewrite.
        update_destruct.
        * exfalso. eapply lifted_no_AE_to_self with (net := net); eauto.
        * unfold update_elections_data_appendEntries. repeat find_rewrite. simpl.
          { find_copy_apply_lem_hyp handleAppendEntries_success_allEntries.
            - break_exists. break_and.
              find_copy_apply_lem_hyp handleAppendEntries_success_term.
              assert (In x (log (snd (nwState net (pSrc p))))).
              { eapply appendEntries_sublog; eauto. subst. repeat find_rewrite. auto. }
              assert (entries_match (log d) (log (snd (nwState net (pSrc p))))).
              { match goal with
                | [ H : refined_raft_intermediate_reachable (mkNetwork ?a ?b) |- _ ] =>
                  let H' := fresh "H" in
                  pose proof entries_match_invariant _ (pDst p) (pSrc p) H as H';
                    simpl in H'; repeat find_higher_order_rewrite; rewrite_update;
                    simpl in H'; auto
                end.
              }
              assert (In e (log d)) as Helogd.
              { match goal with
                | [ H : entries_match _ _ |- _ ] =>
                  specialize (H x x e)
                end.
                repeat concludes. intuition.
              }

              match goal with
              | [ H : refined_raft_intermediate_reachable (mkNetwork ?a ?b) |- _ ] =>
                let H' := fresh "H" in
                pose proof log_all_entries_invariant _ H (pDst p) e as H';
                  simpl in H'; repeat find_higher_order_rewrite; rewrite_update;
                  simpl in H'; unfold update_elections_data_appendEntries in H';
                  repeat find_rewrite; simpl in H'
              end.
              auto.
            - find_apply_lem_hyp lifted_terms_and_indices_from_one_log; auto. break_and.
              apply maxIndex_gt_0_nonempty. omega.
            - intros.
              match goal with
              | [ H : refined_raft_intermediate_reachable (mkNetwork _ _) |- _ ] => clear H
              end.
              pose proof entries_match_nw_host_invariant _ $(eauto)$ _ _ _ _ _ _ _ (pDst p)
                   e0 e' e'' $(eauto)$ $(eauto)$.
              repeat find_rewrite. auto.
            - apply entries_sorted_invariant. auto.
          }
  Admitted.

  Lemma handleAppendEntriesReply_spec :
    forall n st src t es b st' l,
      handleAppendEntriesReply n st src t es b = (st', l) ->
      (type st' = type st /\
       matchIndex st' = matchIndex st /\
       currentTerm st' = currentTerm st) \/
      (currentTerm st' = t /\ type st' = Follower) \/
      (b = true /\
       t = currentTerm st' /\
       type st' = type st /\
       matchIndex st' = assoc_set name_eq_dec (matchIndex st) src
                                  (PeanoNat.Nat.max
                                     (assoc_default name_eq_dec (matchIndex st) src 0) (maxIndex es)) /\
       currentTerm st' = currentTerm st).
  Proof.
    unfold handleAppendEntriesReply.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto.
    - do_bool. intuition.
    - unfold advanceCurrentTerm. break_match; auto.
  Qed.

  Lemma update_nop_fst :
    forall A B f x (v2 : B) y,
      fst (update f x (fst (f x), v2) y) = fst (A := A) (f y).
  Proof.
    intros.
    update_destruct; auto.
  Qed.

  Lemma get_set_diff_default :
    forall K V K_eq_dec (k k' : K) (v : V) l d,
      k <> k' ->
      assoc_default K_eq_dec (assoc_set K_eq_dec l k v) k' d = assoc_default K_eq_dec l k' d.
  Proof.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_diff in * by auto; congruence.
  Qed.

  Lemma get_set_same_default :
    forall K V K_eq_dec (k : K) (v : V) l d,
      assoc_default K_eq_dec (assoc_set K_eq_dec l k v) k d = v.
  Proof.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_same in *; congruence.
  Qed.

  Lemma match_index_all_entries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply match_index_all_entries_inv.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, match_index_all_entries_inv.
    simpl. intros. split.
    - { unfold match_index_all_entries in *. simpl. intros. break_and.
        repeat find_higher_order_rewrite.
        rewrite update_nop_fst.
        update_destruct.
        - find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
          intuition.
          + match goal with
            | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h)
            end.
            repeat find_rewrite. repeat concludes.
            find_erewrite_lem handleAppendEntriesReply_log.
            auto.
          + congruence.
          + repeat find_rewrite.
            match goal with
            | [ H : context [ assoc_default _ (assoc_set _ _ ?x _) ?y _ ]  |- _ ] =>
              destruct (name_eq_dec x y)
            end.
            * subst. rewrite get_set_same_default in *.
              find_apply_lem_hyp app_cons_in.
              find_erewrite_lem handleAppendEntriesReply_log.
              { find_apply_lem_hyp PeanoNat.Nat.max_le. break_or_hyp.
                - match goal with
                  | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) (pSrc p))
                  end. repeat find_rewrite. auto.
                - unfold match_index_all_entries_nw in *.
                  match goal with
                  | [ H : pBody _ = _, H' : _  |- _ ] => eapply H' with (e := e) in H; auto
                  end.
              }
            * rewrite get_set_diff_default in * by auto.
              match goal with
              | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h)
              end.
              repeat find_rewrite. repeat concludes.
              find_erewrite_lem handleAppendEntriesReply_log.
              auto.
        - find_apply_hyp_hyp. congruence.
      }
    - admit.
  Admitted.

  Lemma match_index_all_entries_request_vote :
    refined_raft_net_invariant_request_vote match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_do_leader :
    refined_raft_net_invariant_do_leader match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_do_generic_server :
    refined_raft_net_invariant_do_generic_server match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_reboot :
    refined_raft_net_invariant_reboot match_index_all_entries_inv.
  Admitted.

  Lemma match_index_all_entries_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      match_index_all_entries_inv net.
  Proof.
    intros.
    apply refined_raft_net_invariant'; auto.
    - apply match_index_all_entries_init.
    - apply refined_raft_net_invariant_client_request'_weak.
      apply match_index_all_entries_client_request.
    - apply refined_raft_net_invariant_timeout'_weak.
      apply match_index_all_entries_timeout.
    - apply match_index_all_entries_append_entries.
    - apply refined_raft_net_invariant_append_entries_reply'_weak.
      apply match_index_all_entries_append_entries_reply.
    - apply refined_raft_net_invariant_request_vote'_weak.
      apply match_index_all_entries_request_vote.
    - apply refined_raft_net_invariant_request_vote_reply'_weak.
      apply match_index_all_entries_request_vote_reply.
    - apply refined_raft_net_invariant_do_leader'_weak.
      apply match_index_all_entries_do_leader.
    - apply refined_raft_net_invariant_do_generic_server'_weak.
      apply match_index_all_entries_do_generic_server.
    - apply match_index_all_entries_state_same_packet_subset.
    - apply refined_raft_net_invariant_reboot'_weak.
      apply match_index_all_entries_reboot.
  Qed.

  Instance miaei : match_index_all_entries_interface.
  Proof.
    constructor.
    apply match_index_all_entries_invariant.
  Qed.
End MatchIndexAllEntries.