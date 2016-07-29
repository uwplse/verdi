Require Import DynamicNet.
Require Import Chord.
Require Import ChordProof.
Import List.
Require Import Wf_nat.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Set Bullet Behavior "Strict Subproofs".

Section LabeledChord.
  Variable SUCC_LIST_LEN : nat.
  Variable hash : addr -> id.
  Variable base : list addr.

  Notation msg := (msg addr payload).
  Notation global_state := (global_state addr payload data timeout).
  Notation msgs := (msgs addr payload data timeout).
  Notation e_recv := (e_recv addr payload timeout).
  Notation e_timeout := (e_timeout addr payload timeout).
  Notation trace := (trace addr payload data timeout).
  Notation update := (update addr addr_eq_dec data).
  Notation make_pointer := (make_pointer hash).

  Inductive label :=
  | RecvMsg : addr -> addr -> payload -> label
  | Timeout : addr -> timeout -> label.

  Definition label_eq_dec : forall x y : label, {x = y} + {x <> y}.  
  Proof.
    decide equality; eauto using addr_eq_dec, payload_eq_dec, timeout_eq_dec.
  Defined.

  Notation occ_gst := (occ_gst addr payload data timeout label).
  Notation occurrence := (occurrence addr payload data timeout label).
  Notation recv_handler := (recv_handler SUCC_LIST_LEN hash).
  Notation timeout_handler := (timeout_handler hash).

  Definition timeout_handler_l (h : addr) (st : data) (t : timeout) :=
    (timeout_handler h st t, Timeout h t).

  Definition recv_handler_l (src : addr) (dst : addr) (st : data) (msg : payload) :=
    (recv_handler src dst st msg, RecvMsg src dst msg).

  Notation labeled_step_dynamic := (labeled_step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler_l timeout_handler_l timeout_constraint).
  Notation lb_execution := (lb_execution addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler_l timeout_handler_l timeout_constraint).
  Notation strong_local_fairness := (strong_local_fairness addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler_l timeout_handler_l timeout_constraint).
  Notation weak_local_fairness := (weak_local_fairness addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler_l timeout_handler_l timeout_constraint).
  Notation inf_occurred := (inf_occurred addr payload data timeout label).
  Notation enabled := (enabled addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler_l timeout_handler_l timeout_constraint).
  Notation l_enabled := (l_enabled addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler_l timeout_handler_l timeout_constraint). 
  Notation occurred := (occurred addr payload data timeout label).
  Notation nodes := (nodes addr payload data timeout).
  Notation failed_nodes := (failed_nodes addr payload data timeout).
  Notation sigma := (sigma addr payload data timeout).
  Notation timeouts := (timeouts addr payload data timeout).
  Notation apply_handler_result := (apply_handler_result addr addr_eq_dec payload data timeout timeout_eq_dec).
  Notation update_msgs := (update_msgs addr payload data timeout).
  Notation occ_label := (occ_label addr payload data timeout label).

  (* assuming sigma gst h = Some st *)
  Definition failed_successors (gst : global_state) (st : data) : list pointer :=
    filter (fun p : pointer => In_dec addr_eq_dec (snd p) (failed_nodes gst)) (succ_list st).

  Lemma l_enabled_RecvMsg_In_msgs :
    forall e src dst m d,
      In dst (nodes (occ_gst e)) ->
      ~ In dst (failed_nodes (occ_gst e)) ->
      In (src, (dst, m)) (msgs (occ_gst e)) ->
      sigma (occ_gst e) dst = Some d ->
      l_enabled (RecvMsg src dst m) e.
  Proof.
  move => e src dst m d H_in_n H_in_f H_in H_s.
  find_apply_lem_hyp in_split.
  break_exists.
  rewrite /l_enabled /enabled.
  case H_r: (recv_handler_l src dst d m) => [[[[st ms] newts] clearedts] lb].
  have H_lb: lb = RecvMsg src dst m.
    rewrite /recv_handler_l /= in H_r.
    by tuple_inversion.
  rewrite H_lb {H_lb} in H_r.
  pose gst' := apply_handler_result
                 dst
                 (st, ms, newts, clearedts)
                 (e_recv (src, (dst, m)))
                 (update_msgs (occ_gst e) (x ++ x0)).
  exists gst'.
  by eapply LDeliver_node; eauto.
  Qed.

  Ltac break_labeled_step :=
    match goal with
      | H : labeled_step_dynamic _ _ _ |- _ =>
        destruct H
    end; subst.

  Ltac inv_labeled_step :=
    match goal with
      | H : labeled_step_dynamic _ _ _ |- _ =>
        inv H; try now (unfold recv_handler_l, timeout_handler_l in *; tuple_inversion)
    end.

  Ltac invc_labeled_step :=
    match goal with
      | H : labeled_step_dynamic _ _ _ |- _ =>
        invc H; try now (unfold recv_handler_l, timeout_handler_l in *; tuple_inversion)
    end.

  Lemma sigma_ahr_updates :
    forall gst n st ms nts cts e,
      sigma (apply_handler_result n (st, ms, nts, cts) e gst) n = Some st.
  Proof.
    unfold apply_handler_result, update.
    simpl.
    intuition. 
    break_if; auto || congruence.
  Qed.

  Lemma sigma_ahr_passthrough :
    forall gst n st ms nts cts e h d,
      n <> h ->
      sigma gst h = Some d ->
      sigma (apply_handler_result n (st, ms, nts, cts) e gst) h = Some d.
  Proof.
    unfold apply_handler_result, update.
    simpl.
    intuition. 
    break_if; auto || congruence.
  Qed.

  Lemma labeled_step_preserves_state_existing :
    forall gst gst' l h d,
      sigma gst h = Some d ->
      labeled_step_dynamic gst l gst' ->
      exists d',
        sigma gst' h = Some d'.
  Proof.
    intuition.
    break_labeled_step;
      match goal with
      | H: In ?n (nodes _) |- exists _, sigma _ ?h = _ => destruct (addr_eq_dec n h)
      end;
      subst_max;
      eexists;
      eauto using sigma_ahr_updates, sigma_ahr_passthrough.
  Qed.

  Lemma other_elements_remain_after_removal :
    forall A (l xs ys : list A) (a b : A),
      l = xs ++ b :: ys ->
      In a l ->
      a <> b ->
      In a (xs ++ ys).
  Proof.
    intuition.
    subst_max.
    do_in_app.
    break_or_hyp.
    - intuition.
    - find_apply_lem_hyp in_inv.
      break_or_hyp; auto using in_or_app || congruence.
  Qed.

  Lemma define_msg_from_recv_step_equality :
    forall m d st ms nts cts src dst p,
      recv_handler_l (fst m) (fst (snd m)) d (snd (snd m)) = (st, ms, nts, cts, RecvMsg src dst p) ->
      (m = (src, (dst, p)) /\ fst m = src /\ fst (snd m) = dst /\ snd (snd m) = p).
  Proof.
    unfold recv_handler_l.
    intuition;
      now tuple_inversion.
  Qed.

  Ltac recover_msg_from_recv_step_equality :=
    find_copy_apply_lem_hyp define_msg_from_recv_step_equality;
    break_and.

  Ltac recover_msg_from_recv_step_equality_clear :=
    find_apply_lem_hyp define_msg_from_recv_step_equality;
    break_and.

  Lemma elim_labeled_step_recv :
    forall gst gst' src dst p,
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      exists st xs ys st' ms newts clearedts,
        sigma gst dst = Some st /\
        msgs gst = xs ++ (src, (dst, p)) :: ys /\
        recv_handler_l src dst st p = (st', ms, newts, clearedts, RecvMsg src dst p) /\
        gst' = (apply_handler_result dst
                                     (st', ms, newts, clearedts)
                                     (e_recv (src, (dst, p)))
                                     (update_msgs gst (xs ++ ys))).
  Proof.
    intuition.
    inv_labeled_step.
    recover_msg_from_recv_step_equality.
    repeat find_rewrite.
    repeat eexists; eauto.
  Qed.

  Lemma irrelevant_message_not_removed :
    forall m p dst src to from gst gst',
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      In (from, (to, m)) (msgs gst) ->
      (from, (to, m)) <> (src, (dst, p)) ->
      In (from, (to, m)) (msgs gst').
  Proof.
    intuition.
    inv_labeled_step.
    apply in_or_app.
    right.
    recover_msg_from_recv_step_equality.
    eapply other_elements_remain_after_removal; eauto.
    now repeat find_rewrite.
  Qed.

  Ltac destruct_recv_handler_l :=
    match goal with
      |- context[recv_handler_l ?from ?to ?st ?p] =>
      unfold recv_handler_l;
        destruct (recv_handler from to st p) as [[[?st ?ms] ?cts] ?nts] eqn:?H
    end.

  Lemma when_RecvMsg_enabled :
    forall from to p gst,
      In to (nodes gst) ->
      ~ In to (failed_nodes gst) ->
      (exists st, sigma gst to = Some st) ->
      In (from, (to, p)) (msgs gst) ->
      enabled (RecvMsg from to p) gst.
  Proof.
    intuition.
    find_apply_lem_hyp in_split.
    break_exists.
    match goal with
      | H: sigma ?gst ?to = Some ?d |- enabled (RecvMsg ?from ?to ?p) ?gst =>
        assert (exists st ms nts cts, recv_handler_l from to d p = (st, ms, nts, cts, RecvMsg from to p))
    end.
    destruct_recv_handler_l.
    repeat eexists.
    break_exists.
    unfold enabled.
    eauto using LDeliver_node.
  Qed.

  Lemma recv_implies_state_exists :
    forall gst gst' gst'' from to src dst p m,
      labeled_step_dynamic gst (RecvMsg from to p) gst'  ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      exists st,
        sigma gst' dst = Some st.
  Proof.
    intuition.
    invc_labeled_step.
    invc_labeled_step.
    recover_msg_from_recv_step_equality_clear.
    recover_msg_from_recv_step_equality_clear.
    repeat find_rewrite.
    unfold update_msgs.
    destruct (addr_eq_dec to dst).
    - repeat find_rewrite.
      eauto using sigma_ahr_updates.
    - eauto using sigma_ahr_passthrough.
  Qed.

  Lemma recv_implies_msg_in_before :
    forall gst gst' src dst p,
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      In (src, (dst, p)) (msgs gst).
  Proof.
    intuition.
    invc_labeled_step.
    recover_msg_from_recv_step_equality_clear.
    repeat find_rewrite.
    auto using in_or_app, in_eq.
  Qed.

  Lemma recv_implies_msg_in_after :
    forall gst gst' gst'' dst to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      (src, (dst, m)) <> (from, (to, p)) ->
      In (src, (dst, m)) (msgs gst').
  Proof.
    intuition.
    eapply irrelevant_message_not_removed.
    - eauto.
    - invc_labeled_step.
      invc_labeled_step.
      recover_msg_from_recv_step_equality_clear.
      recover_msg_from_recv_step_equality_clear.
      match goal with
      | H: msgs ?gst = _ ++ ?packet :: _,
        H': ?packet = ?tuple
        |- In ?tuple (msgs ?gst) =>
        rewrite H; rewrite H'
      end.
      auto using in_or_app, in_eq.
    - congruence.
  Qed.

  Ltac construct_gst_RecvMsg :=
    match goal with
    | Hst: sigma ?gst ?d = Some ?st,
      Hmsgs: msgs ?gst = ?xs ++ (?s, (?d, ?p)) :: ?ys
      |- enabled (RecvMsg ?s ?d ?p) ?gst =>
      destruct (recv_handler_l s d st p) as [[[[?st' ?ms] ?nts] ?cts] ?l] eqn:?H;
        remember (apply_handler_result
                    d
                    (st', ms, nts, cts)
                    (e_recv (s, (d, p)))
                    (update_msgs gst (xs ++ ys))) as egst
    end.

  Lemma recv_implies_node_in :
    forall gst gst' src dst p,
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
       In dst (nodes gst).
  Proof.
    intuition.
    invc_labeled_step.
  Qed.

  Lemma recv_implies_node_not_failed :
    forall gst gst' src dst p,
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      ~ In dst (failed_nodes gst).
  Proof.
    intuition.
    invc_labeled_step.
  Qed.

  Lemma failed_nodes_never_added :
    forall gst gst' l h,
      labeled_step_dynamic gst l gst' ->
      ~ In h (failed_nodes gst) ->
      ~ In h (failed_nodes gst').
  Proof.
    intuition.
    now invc_labeled_step.
  Qed.

  Lemma failed_nodes_never_removed :
    forall gst gst' l h,
      labeled_step_dynamic gst l gst' ->
      In h (failed_nodes gst) ->
      In h (failed_nodes gst').
  Proof.
    intuition.
    now invc_labeled_step.
  Qed.

  Lemma nodes_never_removed :
    forall gst gst' l h,
      labeled_step_dynamic gst l gst' ->
      In h (nodes gst) ->
      In h (nodes gst').
  Proof.
    intuition.
    match goal with
    | H: labeled_step_dynamic _ _ _ |- _ => destruct H eqn:?H
    end;
      now invc_labeled_step.
  Qed.

  Lemma labeled_step_dynamic_neq_payload_enabled :
    forall gst gst' gst'' to from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg from to m) gst'' ->
      m <> p ->
      enabled (RecvMsg from to m) gst'.
  Proof.
    intuition.
    apply when_RecvMsg_enabled.
    - eauto using recv_implies_node_in, nodes_never_removed.
    - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
    - eauto using recv_implies_state_exists.
    - eapply irrelevant_message_not_removed.
      * eauto.
      * eauto using recv_implies_msg_in_before.
      * congruence.
  Qed.

  Lemma labeled_step_dynamic_neq_src_enabled :
    forall gst gst' gst'' to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src to m) gst'' ->
      src <> from ->
      enabled (RecvMsg src to m) gst'.
  Proof.
    intuition.
    apply when_RecvMsg_enabled.
    - eauto using recv_implies_node_in, nodes_never_removed.
    - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
    - eauto using recv_implies_state_exists.
    - eapply irrelevant_message_not_removed.
      * eauto.
      * eauto using recv_implies_msg_in_before.
      * congruence.
  Qed.
  
  Lemma labeled_step_dynamic_neq_dst_enabled :
    forall gst gst' gst'' dst to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      dst <> to ->
      enabled (RecvMsg src dst m) gst'.
  Proof.
    intuition.
    apply when_RecvMsg_enabled.
    - eauto using recv_implies_node_in, nodes_never_removed.
    - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
    - eauto using recv_implies_state_exists.
    - eapply irrelevant_message_not_removed.
      * eauto.
      * eauto using recv_implies_msg_in_before.
      * congruence.
  Qed.

  Lemma recv_implies_state_exists_after_timeout :
    forall gst gst' gst'' h t src dst m,
      labeled_step_dynamic gst (Timeout h t) gst'  ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      exists st,
        sigma gst' dst = Some st.
  Proof.
    intuition.
    invc_labeled_step.
    invc_labeled_step.
    match goal with
    | |- context[sigma (apply_handler_result ?h _ _ _) ?dst] =>
      destruct (addr_eq_dec h dst)
    end.
    - subst.
      eauto using sigma_ahr_updates.
    - recover_msg_from_recv_step_equality_clear.
      repeat find_rewrite.
      eauto using sigma_ahr_passthrough.
  Qed.

  Lemma recv_implies_message_exists_after_timeout :
    forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    In (src, (dst, m)) (msgs gst').
  Proof.
    intuition.
    find_copy_eapply_lem_hyp recv_implies_msg_in_before.
    invc_labeled_step.
    invc_labeled_step.
    recover_msg_from_recv_step_equality_clear.
    apply in_or_app.
    right.
    assumption.
  Qed.

  Lemma labeled_step_dynamic_timeout_enabled :
    forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    enabled (RecvMsg src dst m) gst'.
  Proof.
    intuition.
    apply when_RecvMsg_enabled.
    - eauto using recv_implies_node_in, nodes_never_removed.
    - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
    - eauto using recv_implies_state_exists_after_timeout.
    - eauto using recv_implies_message_exists_after_timeout.
  Qed.

  Lemma RecvMsg_enabled_until_occurred :
    forall s, lb_execution s ->
      forall src dst m, l_enabled (RecvMsg src dst m) (hd s) ->
        weak_until (now (l_enabled (RecvMsg src dst m)))
              (now (occurred (RecvMsg src dst m)))
              s.
  Proof.
    cofix c.
    case => /=.
    case => /= gst.
    case => [from to p|h t].
    - case.
      case => /= gst' lb' s H_exec src dst m H_en.
      inversion H_exec; subst_max.
      simpl in *.
      case (addr_eq_dec dst to) => H_dec_dst.
        case (addr_eq_dec src from) => H_dec_src.
          case (payload_eq_dec m p) => H_dec_m.
            subst_max.
            exact: W0.
          subst_max.
          apply: W_tl; first by [].
          apply: c => //=.
          unfold l_enabled in *.
          simpl in *.
          unfold enabled in H_en.
          break_exists.
          move: H1 H H_dec_m.
          exact: labeled_step_dynamic_neq_payload_enabled.
        subst_max.
        apply: W_tl; first by [].
        apply: c => //=.
        unfold l_enabled in *.
        simpl in *.
        unfold enabled in H_en.
        break_exists.
        move: H1 H H_dec_src.
        exact: labeled_step_dynamic_neq_src_enabled.
      apply: W_tl; first by [].
      apply: c => //=.
      unfold l_enabled in *.
      simpl in *.
      unfold enabled in H_en.
      break_exists.
      move: H1 H H_dec_dst.
      exact: labeled_step_dynamic_neq_dst_enabled.
    - case.
      case => /= gst' lb' s H_exec src dst m H_en.
      inversion H_exec; subst_max.
      simpl in *.
      rewrite /l_enabled /= in H_en.
      apply: W_tl; first by [].
      apply: c => //=.
      unfold l_enabled in *.
      simpl in *.
      unfold enabled in H_en.
      break_exists.
      move: H1 H.
      exact: labeled_step_dynamic_timeout_enabled.
  Qed.

  Lemma RecvMsg_eventually_occurred :
    forall s, lb_execution s ->
         weak_local_fairness s ->
         forall src dst m d, 
           In dst (nodes (occ_gst (hd s))) ->
           ~ In dst (failed_nodes (occ_gst (hd s))) ->
           In (src, (dst, m)) (msgs (occ_gst (hd s))) ->
           sigma (occ_gst (hd s)) dst = Some d ->
           eventually (now (occurred (RecvMsg src dst m))) s.
  Proof.
    move => s H_exec H_fair src dst m d H_in_n H_in_f H_in_m H_s.
    have H_un := RecvMsg_enabled_until_occurred _ H_exec src dst m.
    apply weak_until_until_or_always in H_un; last by apply: l_enabled_RecvMsg_In_msgs; eauto.
    case: H_un; first exact: until_eventually.
    move => H_al.
    apply always_continuously in H_al.
    apply H_fair in H_al.
    destruct s as [x s].
    by apply always_now in H_al.
  Qed.

  Lemma timeout_step_satisfies_constraint :
    forall gst h t gst',
      labeled_step_dynamic gst (Timeout h t) gst' ->
      timeout_constraint gst h t.
  Proof.
    move => gst h t gst' H_step.
    now invc_labeled_step.
  Qed.

  Lemma when_Timeout_enabled :
    forall h t st gst,
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = Some st ->
      In t (timeouts gst h) ->
      timeout_constraint gst h t ->
      enabled (Timeout h t) gst.
  Proof.
    move => h t st gst H_in H_live H_st H_t H_constraint.
    unfold enabled.
    case H_r: (timeout_handler_l h st t) => [[[[st' ms] nts] cts] l].
    pose gst' := apply_handler_result
                   h
                   (st', ms, nts, t :: cts)
                   (e_timeout h t)
                   gst.
    have H_l: l = Timeout h t.
      rewrite /timeout_handler_l /= in H_r.
      by tuple_inversion.
    subst_max.
    exists gst'.
    now eapply LTimeout; eauto.
  Qed.

  Lemma timeout_implies_node_exists :
    forall gst h t gst',
      labeled_step_dynamic gst (Timeout h t) gst' ->
      In h (nodes gst).
  Proof.
    intuition.
    invc_labeled_step.
  Qed.

  Lemma timeout_implies_node_not_failed :
    forall gst h t gst',
      labeled_step_dynamic gst (Timeout h t) gst' ->
      ~ In h (failed_nodes gst).
  Proof.
    intuition.
    invc_labeled_step.
  Qed.

  Lemma timeout_implies_state_exists :
    forall gst h t gst',
      labeled_step_dynamic gst (Timeout h t) gst' ->
      exists st,
        sigma gst h = Some st.
  Proof.
    intuition.
    invc_labeled_step.
    unfold timeout_handler_l in *.
    tuple_inversion.
    by eauto.
  Qed.

  Lemma update_characterization : forall f x y,
      update f x y x = Some y.
  Proof.
    intuition.
    unfold update.
    case (addr_eq_dec x x) => //.
  Qed.

  Lemma states_not_removed_by_recv_step :
    forall gst gst' h st src dst p,
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      sigma gst h = Some st ->
      exists d,
        sigma gst' h = Some d.
  Proof.
    move => gst gst' h st src dst p H_step H_st.
    invc_labeled_step.
    recover_msg_from_recv_step_equality_clear.
    simpl.
    repeat find_rewrite.
    case (addr_eq_dec h dst).
    - move => H_eq.
      subst_max.
      eexists.
      exact: update_characterization.
    - move => H_neq.
      exists st.
      rewrite <- H_st.
      move: H_neq.
      exact: update_fixes_other_arguments.
  Qed.

  Lemma timeout_step_implies_timeout_exists :
    forall gst gst' h t,
      labeled_step_dynamic gst (Timeout h t) gst' ->
      In t (timeouts gst h).
  Proof.
    intuition.
    invc_labeled_step.
  Qed.

  Lemma recv_handler_keeps_timeouts_satisfying_constraint :
   forall gst src dst p gst' t h,
     labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
     In t (timeouts gst h) ->
     timeout_constraint gst h t ->
     In t (timeouts gst' h).
  Admitted.

  Lemma request_constraint_prevents_recv_adding_msgs :
    forall gst from to m gst' h dst p gst'' q,
    labeled_step_dynamic gst (RecvMsg from to m) gst' ->
    labeled_step_dynamic gst (Timeout h (Request dst p)) gst'' ->
    request_response_pair p q ->
    ~ In (dst, (h, q)) (msgs gst) ->
    ~ In (dst, (h, q)) (msgs gst').
  Admitted.

  Lemma labeled_step_dynamic_recv_timeout_enabled :
    forall gst gst' gst'' a b m h t,
      labeled_step_dynamic gst (RecvMsg a b m) gst' ->
      labeled_step_dynamic gst (Timeout h t) gst'' ->
      enabled (Timeout h t) gst'.
  Proof.
    move => gst gst' gst'' a b m h t H_recv H_timeout.
    find_copy_apply_lem_hyp timeout_step_satisfies_constraint.
    find_copy_apply_lem_hyp timeout_implies_state_exists.
    break_exists_name st.
    copy_eapply states_not_removed_by_recv_step H_recv; eauto.
    break_exists_name st'.
    eapply when_Timeout_enabled.
    - find_apply_lem_hyp timeout_implies_node_exists.
      move: H_recv H_timeout.
      exact: nodes_never_removed.
    - find_apply_lem_hyp timeout_implies_node_not_failed.
      move: H_recv H_timeout.
      exact: failed_nodes_never_added.
    - by eauto.
    - invc_labeled_step.
      inv_labeled_step.
      eapply recv_handler_keeps_timeouts_satisfying_constraint; eauto.
      (* TODO make this a lemma/tactic like recover_msg_from_... *)
      unfold timeout_handler_l in *.
      now tuple_inversion.
    - match goal with
      | H: timeout_constraint _ _ _ |- _ => invc H
      end.
      * apply Tick_unconstrained.
      * apply Request_needs_dst_dead_and_no_msgs.
        + eapply failed_nodes_never_removed; eauto.
        + move => q H_pair.
          now eapply request_constraint_prevents_recv_adding_msgs; eauto.
  Qed.

  Lemma labeled_step_dynamic_timeout_neq_h_timeout_enabled :
    forall gst gst' gst'' h h' t t',
      labeled_step_dynamic gst (Timeout h t) gst' ->
      labeled_step_dynamic gst (Timeout h' t') gst'' ->
      h <> h' ->
      enabled (Timeout h' t') gst'.
  Admitted.

  Lemma labeled_step_dynamic_timeout_neq_timeout_enabled :
    forall gst gst' gst'' h h' t t',
      labeled_step_dynamic gst (Timeout h t) gst' ->
      labeled_step_dynamic gst (Timeout h' t') gst'' ->
      t <> t' ->
      enabled (Timeout h' t') gst'.
  Admitted.

  Lemma Timeout_enabled_until_occurred :
    forall s h t,
      lb_execution s ->
      l_enabled (Timeout h t) (hd s) ->
      weak_until (now (l_enabled (Timeout h t)))
                 (now (occurred (Timeout h t)))
              s.
  Proof.
    cofix c.
    case => /=.
    case => /= gst.
    case => [from to p|h t].
    - case.
      case => /= gst' lb' s h t H_exec H_en.
      inversion H_exec as [o o' s' H_step_recv H_exec' H_oeq]; subst_max.
      simpl in *.
      case (addr_eq_dec h to) => H_dec_h.
      * subst_max.
        apply: W_tl => //.
        apply: c => //=.
        unfold l_enabled in *.
        unfold enabled in H_en.
        break_exists_name gst''.
        move: H_step_recv H_en.
        simpl in *.
        exact: labeled_step_dynamic_recv_timeout_enabled.
      * apply: W_tl => //.
        apply: c => //=.
        unfold l_enabled in *.
        unfold enabled in H_en.
        break_exists_name gst''.
        move: H_step_recv H_en.
        exact: labeled_step_dynamic_recv_timeout_enabled.
    - case.
      case => /= gst' l s h' t' H_exec H_en.
      inversion H_exec as [o o' s' H_step_timeout H_exec' H_oeq]; subst_max.
      simpl in *.
      case (addr_eq_dec h h') => H_dec_h.
      * subst_max.
        case (timeout_eq_dec t t') => H_dec_t.
        + subst_max.
          exact: W0.
        + apply W_tl; first by [].
          apply: c => //=.
          unfold l_enabled in *.
          unfold enabled in H_en.
          break_exists_name gst''.
          simpl in *.
          move: H_step_timeout H_en H_dec_t.
          exact: labeled_step_dynamic_timeout_neq_timeout_enabled.
      * apply W_tl; first by [].
        apply: c => //=.
        unfold l_enabled in *.
        unfold enabled in H_en.
        break_exists_name gst''.
        move: H_step_timeout H_en H_dec_h.
        exact: labeled_step_dynamic_timeout_neq_h_timeout_enabled.
  Qed.

  Lemma l_enabled_Timeout_In_timeouts :
    forall h t e st,
      In h (nodes (occ_gst e)) ->
      ~ In h (failed_nodes (occ_gst e)) ->
      In t (timeouts (occ_gst e) h) ->
      sigma (occ_gst e) h = Some st ->
      timeout_constraint (occ_gst e) h t ->
      l_enabled (Timeout h t) e.
  Proof.
    move => h t e st H_node H_live H_t H_st.
    unfold l_enabled, enabled.
    set (gst := occ_gst e) in *.
    case H_r: (timeout_handler_l h st t) => [[[[st' ms] newts] clearedts] lb].
    rewrite /timeout_handler_l /= in H_r.
    have H_lb: lb = Timeout h t by tuple_inversion.
    rewrite H_lb {H_lb} in H_r.
    pose gst' := apply_handler_result
                   h
                   (st', ms, newts, t :: clearedts)
                   (e_timeout h t)
                   gst.
    exists gst'.
    by eapply LTimeout; eauto.
  Qed.

  Lemma unconstrained_timeout_eventually_occurred :
    forall s,
      lb_execution s ->
      weak_local_fairness s ->
      forall h st t,
        In t (timeouts (occ_gst (hd s)) h) ->
        In h (nodes (occ_gst (hd s))) ->
        ~ In h (failed_nodes (occ_gst (hd s))) ->
        sigma (occ_gst (hd s)) h = Some st ->
        timeout_constraint (occ_gst (hd s)) h t ->
        eventually (now (occurred (Timeout h t))) s.
  Proof.
    move => s H_exec H_fair h st t H_in_n H_in_f H_in_m H_s H_constraint.
    have H_un := Timeout_enabled_until_occurred _ h t H_exec.
    apply weak_until_until_or_always in H_un;
      last by eapply l_enabled_Timeout_In_timeouts; eauto.
    case: H_un; first exact: until_eventually.
    move => H_al.
    apply always_continuously in H_al.
    apply H_fair in H_al.
    destruct s as [x s].
    by apply always_now in H_al.
  Qed.

  Definition res_clears_timeout (r : res) (t : timeout) : Prop :=
    match r with
    | (_, _, _, cts) => In t cts
    end.

  Inductive clears_timeout (h : addr) (t : timeout) (o : occurrence) : Prop :=
  | ct_Timeout : forall st t',
      sigma (occ_gst o) h = Some st ->
      occ_label o = Timeout h t' ->
      res_clears_timeout (timeout_handler h st t') t ->
      clears_timeout h t o
  | ct_RecvMsg : forall st src p,
      sigma (occ_gst o) h = Some st ->
      occ_label o = RecvMsg src h p ->
      res_clears_timeout (recv_handler src h st p) t ->
      clears_timeout h t o.

  Lemma constrained_Request_conditions :
    forall gst h dst p st,
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = st ->
      ~ timeout_constraint gst h (Request dst p) ->
      ~ In dst (failed_nodes gst) \/
      exists m : payload,
        request_response_pair p m /\ In (dst, (h, m)) (msgs gst).
  Admitted.

  Lemma response_clears_timeout :
    forall s p m h dst,
      lb_execution s ->
      request_response_pair p m ->
      eventually (now (occurred (RecvMsg dst h m))) s ->
      eventually (now (clears_timeout h (Request dst p))) s.
  Admitted.

  Lemma requests_eventually_get_responses :
    forall s,
      lb_execution s ->
      weak_local_fairness s ->
      forall src dst m p,
        In src (nodes (occ_gst (hd s))) ->
        ~ In src (failed_nodes (occ_gst (hd s))) ->
        In dst (nodes (occ_gst (hd s))) ->
        request_response_pair p m ->
        (~ In dst (failed_nodes (occ_gst (hd s))) /\
         In (src, (dst, p)) (msgs (occ_gst (hd s)))) \/
        In (dst, (src, m)) (msgs (occ_gst (hd s))) ->
        In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
        eventually (now (occurred (RecvMsg dst src m))) s.
  Admitted.

  Lemma queries_are_closed_by_recvmsg :
    forall o src dst p m,
      request_response_pair p m ->
      In (Request dst p) (timeouts (occ_gst o) src) ->
      occ_label o = RecvMsg dst src m ->
      clears_timeout src (Request dst p) o.
  Admitted.

  Lemma queries_now_closed :
    forall p m dst src s,
      request_response_pair p m ->
      In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
      eventually (now (occurred (RecvMsg dst src m))) s ->
      eventually (now (clears_timeout src (Request dst p))) s.
  Admitted.

  Definition Request_has_unique_message (gst : global_state) : Prop :=
    forall src dst p m,
      In (Request dst p) (timeouts gst src) ->
      request_response_pair p m ->
      (~ In dst (failed_nodes gst) /\
       In (src, (dst, p)) (msgs gst)) \/
      In (dst, (src, m)) (msgs gst).

  Lemma requests_eventually_complete :
    forall s,
      lb_execution s ->
      weak_local_fairness s ->
      forall src dst p m,
        In src (nodes (occ_gst (hd s))) ->
        ~ In src (failed_nodes (occ_gst (hd s))) ->
        In dst (nodes (occ_gst (hd s))) ->
        request_response_pair p m ->
        (~ In dst (failed_nodes (occ_gst (hd s))) /\
         In (src, (dst, p)) (msgs (occ_gst (hd s)))) \/
        In (dst, (src, m)) (msgs (occ_gst (hd s))) ->
        In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
        eventually (now (clears_timeout src (Request dst p))) s.
  Proof.
    intros.
    find_copy_eapply_lem_hyp requests_eventually_get_responses; eauto.
    eapply queries_now_closed; eauto.
  Qed.

  Lemma not_timeout_constraint_inv :
    forall gst src dst p,
      ~ timeout_constraint gst src (Request dst p) ->
      ~ In dst (failed_nodes gst) \/
      exists m,
        request_response_pair p m /\ In (dst, (src, m)) (msgs gst).
  Admitted.

  Definition Request_payload_has_response (gst : global_state) : Prop :=
    forall src dst p,
      In (Request dst p) (timeouts gst src) ->
      exists m,
        request_response_pair p m.

  Lemma constrained_timeout_eventually_cleared :
    forall s,
      lb_execution s ->
      weak_local_fairness s ->
      (* this is an inductive invariant conjunct *)
      timeouts_match_msg (occ_gst (hd s)) ->
      Request_goes_to_real_node (occ_gst (hd s)) ->
      Request_payload_has_response (occ_gst (hd s)) ->
      Request_has_unique_message (occ_gst (hd s)) ->
      forall h st t,
        In t (timeouts (occ_gst (hd s)) h) ->
        In h (nodes (occ_gst (hd s))) ->
        ~ In h (failed_nodes (occ_gst (hd s))) ->
        sigma (occ_gst (hd s)) h = Some st ->
        ~ timeout_constraint (occ_gst (hd s)) h t ->
        eventually (now (clears_timeout h t)) s.
  Proof.
    move => s H_exec H_fair H_inv H_reqnode H_res H_uniqm h st t H_t H_node H_live H_st H_constraint.
    destruct t.
    - (* Tick case is.. impossible *)
      exfalso.
      apply: H_constraint.
      exact: Tick_unconstrained.
    - find_copy_eapply_lem_hyp not_timeout_constraint_inv.
      break_or_hyp.
      * copy_apply H_reqnode H_t.
        copy_apply H_res H_t.
        break_exists.
        eapply requests_eventually_complete; eauto.
      * break_exists.
        break_and.
        eapply requests_eventually_complete; eauto.
  Qed.

Lemma always_in_nodes :
  forall s, lb_execution s ->
       forall h, In h (nodes (occ_gst (hd s))) ->
       always (now (fun o => In h (nodes (occ_gst o)))) s.
Proof.
cofix c.
case => /= o; case => o' s H_exec h H_in_f.
inversion H_exec; subst.
apply: Always; first by [].
rewrite /=.
apply: c; first by [].
rewrite /=.
by apply: nodes_never_removed; eauto.
Qed.

Lemma always_not_failed :
  forall s, lb_execution s ->
       forall h, ~ In h (failed_nodes (occ_gst (hd s))) ->
       always (now (fun o => ~ In h (failed_nodes (occ_gst o)))) s.
Proof.
cofix c.
case => /= o; case => o' s H_exec h H_in_f.
inversion H_exec; subst.
apply: Always; first by [].
rewrite /=.
apply: c; first by [].
rewrite /=.
by apply: failed_nodes_never_added; eauto.
Qed.

Lemma failed_successors_le_monotonic :   
  forall gst gst' l h d d' k,
    sigma gst h = Some d ->
    length (failed_successors gst d) <= k ->
    labeled_step_dynamic gst l gst' ->
    sigma gst' h = Some d' -> 
    length (failed_successors gst' d') <= k.
Proof.
Admitted.

Lemma lb_execution_failed_successors_le_monotonic :
  forall s, lb_execution s ->
       forall h d, sigma (occ_gst (hd s)) h = Some d ->
       forall k, length (failed_successors (occ_gst (hd s)) d) <= k ->
       always (now (fun o => forall d', sigma (occ_gst o) h = Some d' -> length (failed_successors (occ_gst o) d') <= k)) s.
Proof.
cofix c.
case => o; case => o' s H_exec h d H_eq k H_len.
inversion H_exec; subst.
apply Always => /=; first by move => d' H_eq'; rewrite H_eq in H_eq'; find_injection.
simpl in *.
have [d' H_d'] := labeled_step_preserves_state_existing _ _ _ _ _ H_eq H1.
have H_k := failed_successors_le_monotonic _ _ _ _ _ _ _ H_eq H_len H1 H_d'.
by apply: c; eauto.
Qed.

Lemma eventually_fewer_failed_successors : 
  forall s, lb_execution s ->
       weak_local_fairness s ->
       forall h, In h (nodes (occ_gst (hd s))) ->
            ~ In h (failed_nodes (occ_gst (hd s))) ->
       forall d, sigma (occ_gst (hd s)) h = Some d ->
       forall k, length (failed_successors (occ_gst (hd s)) d) = S k ->
       eventually (now (fun o => forall d', sigma (occ_gst o) h = Some d' -> length (failed_successors (occ_gst o) d') = k)) s.
Proof.
Admitted.

Lemma eventually_zero_failed_successors :
  forall s, lb_execution s ->
       weak_local_fairness s ->
       forall h, In h (nodes (occ_gst (hd s))) ->
            ~ In h (failed_nodes (occ_gst (hd s))) ->
            forall d, sigma (occ_gst (hd s)) h = Some d ->
       eventually (now (fun o => forall d', sigma (occ_gst o) h = Some d' -> length (failed_successors (occ_gst o) d') = 0)) s.
Proof.
move => s H_exec H_fair h H_in H_in_f d H_eq.
have H_ex: exists k, length (failed_successors (occ_gst (hd s)) d) = k.
  case length; first by exists 0.
  move => k.
  by exists (S k).
break_exists.
elim/(well_founded_ind lt_wf): x s H_exec H_fair H_in H_in_f d H_eq H.
case => [|k] IH s H_exec H_fair H_in H_in_f d H_eq H_len.
  apply: E0.
  destruct s.
  simpl in *.
  move => d' H_eq'.
  rewrite H_eq in H_eq'.
  by find_injection.
have H_k: k < S k by auto.
have IH' := IH _ H_k.
have H_ev := eventually_fewer_failed_successors _ H_exec H_fair _ H_in H_in_f _ H_eq _ H_len.
move {H_len}.
elim: H_ev H_exec H_fair H_in H_in_f d H_eq.
  move => s0 H_now H_exec H_fair H_in H_in_f d H_eq.
  apply: IH' => //; eauto.
  destruct s0.
  simpl in *.
  exact: H_now.
move => o s0 H_ev H_ev' H_exec H_fair H_in H_in_f d H_eq.
apply: E_next.
inversion H_exec; subst.
simpl in *.
have [d' H_d'] := labeled_step_preserves_state_existing _ _ _ _ _ H_eq H1.
apply: H_ev'; eauto.
- by apply weak_local_fairness_invar in H_fair.
- by apply: nodes_never_removed; eauto.
- by apply: failed_nodes_never_added; eauto.
Qed.

Lemma continuously_live_successors :
  forall s, lb_execution s ->
       weak_local_fairness s ->
       forall h, In h (nodes (occ_gst (hd s))) ->
            ~ In h (failed_nodes (occ_gst (hd s))) ->
       forall d, sigma (occ_gst (hd s)) h = Some d ->
       continuously (now (fun o => forall d', sigma (occ_gst o) h = Some d' -> length (failed_successors (occ_gst o) d') = 0)) s.
Proof.
move => s H_exec H_fair h H_in H_in_f d H_eq.
have H_ev := eventually_zero_failed_successors _ H_exec H_fair _ H_in H_in_f _ H_eq.
move: H_exec H_fair {H_in H_in_f}.
elim: H_ev d H_eq.
  move => s0 H_now d H_eq H_exec H_fair.
  apply: E0.
  inversion H_exec; subst.
  simpl in *.
  have H_len := H_now _ H_eq.
  have H_le : length (failed_successors (occ_gst o) d) <= 0 by rewrite H_len.
  have H_mon := lb_execution_failed_successors_le_monotonic _ H_exec _ _ H_eq _ H_le.
  move: H_mon.
  apply: always_monotonic.
  case => /= o0 s0 H_le' d' H_eq'.
  apply H_le' in H_eq'.
  by auto with arith.
move => o0 s0 H_ev IH d H_eq H_exec H_fair.
apply: E_next.
inversion H_exec; subst.
simpl in *.
have [d' H_d'] := labeled_step_preserves_state_existing _ _ _ _ _ H_eq H1.
apply: IH; eauto.
by apply weak_local_fairness_invar in H_fair.
Qed.

Definition is_best_succ (gst : global_state) (h s : pointer) : Prop :=
  live_node gst (addr_of s) /\
  forall s',
    live_node gst (addr_of s') ->
    ~ between (id_of h) (id_of s') (id_of s).

Definition is_best_pred (gst : global_state) (h p : pointer) : Prop :=
  live_node gst (addr_of p) /\
  forall p',
    live_node gst (addr_of p') ->
    ~ between (id_of p) (id_of p') (id_of h).

Definition is_best_pred_dec :
  forall gst h p,
    {is_best_pred gst h p} + {~ is_best_pred gst h p}.
Admitted.

(* there might be a better way to phrase this, e.g. as an Inductive definition *)
Definition live_node_count (gst : global_state) (s : nat) : Prop :=
  exists l,
    length l = s /\
    (forall n, In n l <-> live_node gst n).

Definition live_nodes (gst : global_state) : list addr :=
  filter (live_node_dec gst) (nodes gst).

Fixpoint best_succ (live_nodes : list pointer) (h : pointer) : option pointer :=
  match live_nodes with
  | n :: rest => if existsb (fun x => between_bool (id_of h) (id_of x) (id_of n)) rest
                 then best_succ rest h
                 else Some n
  | nil => None
  end.

Lemma best_succ_correct :
  forall gst h s lns,
    (forall x, In x (map addr_of lns) <-> In x (live_nodes gst)) ->
    best_succ lns h = Some s ->
    is_best_succ gst h s.
Admitted.

Definition live_pred_err (live_nodes : list pointer) (h p : pointer) :=
  length (filter (fun x => between_bool (id_of p) (id_of x) (id_of h)) live_nodes).

Definition live_succ1_err (live_nodes : list pointer) (h s : pointer) :=
  length (filter (fun x => between_bool (id_of h) (id_of x) (id_of s)) live_nodes).

Definition pred_error (gst : global_state) (h : pointer) (st : data) : nat :=
  let ha := (addr_of h) in
  let lns := (map make_pointer (live_nodes gst)) in
  match (Chord.pred st) with
  | Some p =>
    if live_node_dec gst (addr_of p)
    then live_pred_err lns h p
    else S (length lns)
  | None => length lns
  end.

Definition succ1_error (gst : global_state) (h : pointer) (st : data) : nat :=
  let ha := (addr_of h) in
  let lns := (map make_pointer (live_nodes gst)) in
  match (head (succ_list st)) with
  | Some s1 =>
    if live_node_dec gst (addr_of s1)
    then live_succ1_err lns h s1
    else S (length lns)
  | None => length lns
  end.

Definition further_succ_error (gst : global_state) (h s1 s : pointer) (i : nat) : nat :=
  if live_node_dec gst (addr_of s1)
  then
    match sigma gst (addr_of s1) with
    | Some st =>
      match nth_error (succ_list st) (i - 1) with
      | Some s' => if pointer_eq_dec s s'
                   then 0
                   else 1
      | None => 1
      end
    | None => 1 (* impossible, since it's live *)
    end
  else 1.

Fixpoint further_succs_error_rec (gst : global_state) (h s1 : pointer) (succs : list pointer) (i : nat) : nat :=
  match succs with
  | s :: rest => further_succ_error gst h s1 s i +
                 further_succs_error_rec gst h s1 rest (S i)
  | nil => 0
  end.

Definition further_succs_error (gst : global_state) (h s1 : pointer) (succs : list pointer) : nat :=
  further_succs_error_rec gst h s1 succs 1.

Definition list_sum : list nat -> nat :=
  fold_right Nat.add 0.

Definition local_error (gst : global_state) (h : addr) : nat :=
  match sigma gst h with
  | Some st =>
    let hp := make_pointer h in
    pred_error gst hp st +
    succ1_error gst hp st +
    match succ_list st with
    | s1 :: succs => further_succs_error gst hp s1 succs
    | nil => 0
    end
  | None => 0
  end.

Definition global_error (gst : global_state) : nat :=
  list_sum (map (local_error gst) (live_nodes gst)).

Inductive pred_error_spec (gst : global_state) (h : pointer) (p : option pointer) : nat -> Prop :=
| pred_error_spec_O :
    forall pr,
      p = Some pr ->
      live_node gst (addr_of pr) ->
      is_best_pred gst h pr ->
      pred_error_spec gst h p 0
| pred_error_spec_S :
    forall pr pr' n size,
      p = Some pr ->
      live_node gst (addr_of pr') ->
      pred_error_spec gst h (Some pr') n ->
      is_best_pred gst pr' pr ->
      (* these next two prevent wraparound *)
      live_node_count gst size ->
      S n < size ->
      pred_error_spec gst h p (S n)
| pred_error_spec_None :
    forall size,
      p = None ->
      live_node_count gst size ->
      pred_error_spec gst h p size
| pred_error_spec_nonmember :
    forall pr size,
      p = Some pr ->
      ~ live_node gst (addr_of pr) ->
      live_node_count gst size ->
      pred_error_spec gst h p (S size).

(* the same as pred_error_spec, just in a different direction *)
Inductive succ1_error_spec (gst : global_state) (h : pointer) (s : option pointer) : nat -> Prop :=
| succ1_error_spec_0 :
    forall s1,
      s = Some s1 ->
      live_node gst (addr_of s1) ->
      is_best_succ gst h s1 ->
      succ1_error_spec gst h s 0
| succ1_error_spec_S :
    forall s1 s' n size,
      s = Some s1 ->
      live_node gst (addr_of s') ->
      succ1_error_spec gst h (Some s') n ->
      is_best_succ gst s' s1 ->
      (* these next two prevent wraparound *)
      live_node_count gst size ->
      S n < size ->
      succ1_error_spec gst h s (S n)
| succ1_error_spec_None :
    forall size,
      s = None ->
      live_node_count gst size ->
      succ1_error_spec gst h s size
| succ1_error_spec_nonmember :
    forall s1 size,
      s = Some s1 ->
      ~ live_node gst (addr_of s1) ->
      live_node_count gst size ->
      succ1_error_spec gst h s size.

Inductive further_succ_error_spec (gst : global_state) (h s : pointer) (n : nat) : nat -> Prop :=
| further_succ_error_0 :
    forall st succ_st s1,
      sigma gst (addr_of h) = Some st ->
      head (succ_list st) = Some s1 ->
      live_node gst (addr_of s1) ->
      sigma gst (addr_of s1) = Some succ_st ->
      nth_error (succ_list succ_st) (n - 1) = Some s ->
      further_succ_error_spec gst h s n 0
| further_succ_error_1_dead :
    forall st s1,
      sigma gst (addr_of h) = Some st ->
      head (succ_list st) = Some s1 ->
      ~ live_node gst (addr_of s1) ->
      further_succ_error_spec gst h s n 1
| further_succ_error_1_mismatch :
    forall st succ_st s1,
      sigma gst (addr_of h) = Some st ->
      head (succ_list st) = Some s1 ->
      sigma gst (addr_of s1) = Some succ_st ->
      nth_error (succ_list succ_st) (n - 1) <> Some s ->
      further_succ_error_spec gst h s n 1.
End LabeledChord.
