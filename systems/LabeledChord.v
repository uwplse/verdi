Require Import Chord.
Require Import ChordProof.
Require Import LabeledDynamicNet.
Import List.
Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import mathcomp.ssreflect.ssreflect.

Require Import Classical. (* yuck *)

Set Bullet Behavior "Strict Subproofs".

Section LabeledChord.
  Variable SUCC_LIST_LEN : nat.
  Variable hash : addr -> id.

  Notation msg := (msg addr payload).
  Notation global_state := (global_state addr payload data timeout).
  Notation msgs := (msgs addr payload data timeout).
  Notation e_recv := (e_recv addr payload timeout).
  Notation trace := (trace addr payload data timeout).

  Inductive label :=
  | RecvMsg : addr -> addr -> payload -> label
  | Timeout : addr -> timeout -> label.

  Definition label_eq_dec : forall x y : label, {x = y} + {x <> y}.  
  Proof.
    decide equality; eauto using addr_eq_dec, payload_eq_dec, timeout_eq_dec.
  Defined.

  Notation occ_gst := (occ_gst addr payload data timeout label).
  Notation occurrence := (occurrence addr payload data timeout label).

  Definition timeout_handler (h : addr) (st : data) (t : timeout) :=
    (timeout_handler hash h st t, Timeout h t).

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) :=
    (recv_handler SUCC_LIST_LEN hash src dst st msg, RecvMsg src dst msg).

  (* todo *)
  Variable extra_constraints : gpred addr payload data timeout.
  Hypothesis extra_constraints_all : forall gst, extra_constraints gst.

  Notation labeled_step_dynamic := (labeled_step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler timeout_handler extra_constraints).
  Notation lb_execution := (lb_execution addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler timeout_handler extra_constraints).
  Notation strong_local_fairness := (strong_local_fairness addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler timeout_handler extra_constraints).
  Notation inf_occurred := (inf_occurred addr payload data timeout label).
  Notation enabled := (enabled addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler timeout_handler extra_constraints).
  Notation l_enabled := (l_enabled addr addr_eq_dec payload data timeout timeout_eq_dec label recv_handler timeout_handler extra_constraints).
  Notation occurred := (occurred addr payload data timeout label).
  Notation nodes := (nodes addr payload data timeout).
  Notation failed_nodes := (failed_nodes addr payload data timeout).
  Notation sigma := (sigma addr payload data timeout).
  Notation apply_handler_result := (apply_handler_result addr addr_eq_dec payload data timeout timeout_eq_dec).
  Notation update_msgs := (update_msgs addr payload data timeout).

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
  case H_r: (recv_handler src dst d m) => [[[[st ms] newts] clearedts] lb].
  have H_lb: lb = RecvMsg src dst m.
    rewrite /recv_handler /= in H_r.
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
        inv H
    end.

  Ltac invc_labeled_step :=
    match goal with
      | H : labeled_step_dynamic _ _ _ |- _ =>
        invc H
    end.

  Lemma labeled_step_preserves_state_existing :
    forall gst gst' l h d,
      sigma gst h = Some d ->
      labeled_step_dynamic gst l gst' ->
      exists d',
        sigma gst' h = Some d'.
  Proof.
    intuition.
    break_labeled_step.
    - destruct (addr_eq_dec h0 h) as [H_eq | H_neq].
      * subst_max.
        exists st'.
        unfold apply_handler_result, update.
        simpl.
        break_if; eauto || congruence.
      * exists d.
        unfold apply_handler_result, update.
        simpl.
        break_if; eauto || congruence.
    - remember (fst (snd m)) as h0.
      destruct (addr_eq_dec h0 h) as [H_eq | H_neq].
      * subst_max.
        exists st.
        unfold apply_handler_result, update.
        simpl.
        break_if; eauto || congruence.
      * exists d.
        unfold apply_handler_result, update.
        simpl.
        break_if; eauto || congruence.
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

  Lemma irrelevant_message_not_removed :
    forall m p dst src to from gst gst',
      In (from, (to, m)) (msgs gst) ->
      m <> p ->
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      In (from, (to, m)) (msgs gst').
  Proof.
    intuition.
    inv_labeled_step.
    - unfold timeout_handler in *.
      tuple_inversion.
    - apply in_or_app.
      right.
      destruct m0 as [s0 [d0 p0]].
      unfold recv_handler in *.
      repeat tuple_inversion.
      eapply other_elements_remain_after_removal.
      * match goal with
        | H : msgs gst = _ ++ _ :: _ |- _ => apply H
        end.
      * auto.
      * intuition.
        tuple_inversion.
        auto.
  Qed.
  
  Lemma labeled_step_dynamic_neq_payload_enabled :
    forall gst gst' gst'' to from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg from to m) gst'' ->
      m <> p ->
      enabled (RecvMsg from to m) gst'.
  Proof.
    intuition.
    inversion H0.
    - unfold timeout_handler in *.
      tuple_inversion.
    - assert (H_m0: m0 = (from, (h, m))).
      * destruct m0.
        destruct p0.
        unfold recv_handler in *.
        tuple_inversion.
        auto.
      * subst_max.
        unfold fst, snd in *.
        inversion H.
        unfold timeout_handler in *.
        tuple_inversion.
        assert (H_m0: m0 = (from, (to, p))).
        unfold recv_handler in *.
        destruct m0.
        destruct p0.
        tuple_inversion.
        auto.
        unfold fst, snd in *.
        assert (H_st: exists d, sigma gst' to = Some d).
        + unfold recv_handler in *.
          repeat tuple_inversion.
          eauto using labeled_step_preserves_state_existing.
        + break_exists.
          remember (recv_handler from to x m) as res.
          symmetry in Heqres.
          destruct res.
          destruct r.
          destruct p0.
          destruct p0.
          assert (H_in: In (from, (to, m)) (msgs gst')).
          unfold recv_handler in *.
          repeat tuple_inversion.
          eapply irrelevant_message_not_removed.
          -- match goal with
             | H: msgs gst = _ |- _ => rewrite H
             end.
             apply in_or_app.
             right.
             apply in_eq.
          -- eauto.
          -- repeat find_rewrite.
             eauto.
          -- find_eapply_lem_hyp in_split.
             break_exists.
             remember (apply_handler_result
                         to
                         (d1, l2, l1, l0)
                         (e_recv (from, (to, m)))
                         (update_msgs gst' (x0 ++ x1))) as egst.
             unfold enabled.
             exists egst.
             subst_max.
             eapply LDeliver_node; eauto.
             simpl.
             unfold fst, snd, recv_handler in *.
             repeat find_rewrite.
             repeat tuple_inversion.
             auto.
  Qed.

  Lemma labeled_step_dynamic_neq_src_enabled :
    forall gst gst' gst'' to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src to m) gst'' ->
      src <> from ->
      enabled (RecvMsg src to m) gst'.
  Proof.
    intuition.
    invc_labeled_step.
    - unfold timeout_handler in *; tuple_inversion.
    - inv_labeled_step.
      * unfold timeout_handler in *; tuple_inversion.
      * repeat match goal with
        | m : msg |- _ => destruct m as [?src [?dst ?p]]
        end.
        unfold fst, snd in *.
        match goal with
        | |- enabled (RecvMsg _ ?to _) ?gst' =>
          remember gst';
          assert (exists x, sigma gst' to = Some x)
        end.
        eapply labeled_step_preserves_state_existing.
        unfold recv_handler in *.
        repeat tuple_inversion.
        eauto.
        repeat find_rewrite; eauto.
        break_exists.

        assert (exists st, sigma g to = Some st).
        unfold recv_handler in *; repeat tuple_inversion.
        eapply labeled_step_preserves_state_existing; eauto.

        break_exists.
        match goal with
          | H: sigma g to = Some ?d |- _ =>
            destruct (recv_handler src to d m)
                     as [[[[?st ?ms] ?nts ] ?cts] ?l] eqn:?H
        end.

        match goal with
        | |- enabled (RecvMsg ?from ?to ?m) ?gst =>
          assert (In (from, (to, m)) (msgs gst))
        end.
        subst.
        unfold apply_handler_result, update_msgs; simpl.
        apply in_or_app; right.
        eapply other_elements_remain_after_removal; eauto.
        unfold recv_handler in *; repeat tuple_inversion.
        repeat find_rewrite.
        apply in_or_app; right.
        auto with *.
        unfold recv_handler in *; repeat tuple_inversion.
        destruct (addr_eq_dec src from);
          intuition;
          tuple_inversion;
          congruence.

        find_copy_apply_lem_hyp in_split.
        break_exists.
        match goal with
          | H : recv_handler src to ?d m = (?st, ?ms, ?nts, ?cts, ?l) |- _ =>
            remember (apply_handler_result
                        to
                        (st, ms, nts, cts)
                        (e_recv (src, (to, m)))
                        (update_msgs g (x1 ++ x2))) as egst
        end.
        exists egst.
        eapply LDeliver_node; eauto; simpl.
        + subst.
          unfold apply_handler_result, recv_handler in *; simpl.
          repeat tuple_inversion.
          auto.
        + subst.
          unfold apply_handler_result, recv_handler in *.
          repeat tuple_inversion.
          auto.
        + repeat find_rewrite.
          unfold recv_handler in *.
          now tuple_inversion.
  Qed.

  Lemma recv_implies_state_exists :
    forall gst gst' gst'' from to src dst p m,
      labeled_step_dynamic gst (RecvMsg from to p) gst'  ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      dst <> to ->
      exists st,
        sigma gst' dst = Some st.
  Proof.
    intuition.
    invc_labeled_step.
    - unfold timeout_handler in *; find_inversion.
    - invc_labeled_step.
      * unfold timeout_handler in *; find_inversion.
      * unfold apply_handler_result, update_msgs, update; simpl.
        break_if; eauto.
        unfold recv_handler in *; repeat tuple_inversion.
        match goal with
        | H: sigma ?gst ?dst = Some ?st |- exists _, sigma ?gst ?dst = Some _ =>
          exists st; auto
        end.
  Qed.

  Lemma recv_implies_msg_in :
    forall gst gst' gst'' dst to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      dst <> to ->
      In (src, (dst, m)) (msgs gst').
  Proof.
    intuition.
    invc_labeled_step.
    - unfold timeout_handler in *; find_inversion.
    - invc_labeled_step.
      * unfold timeout_handler in *; find_inversion.
      * unfold apply_handler_result, update_msgs; simpl.
        unfold recv_handler in *; repeat tuple_inversion.
        unfold fst, snd; repeat break_let.
        apply in_or_app; right.
        eapply other_elements_remain_after_removal; eauto.
        + match goal with
          | H: msgs ?gst = ?xs ++ ?m :: ?ys |- context[ ?m ] =>
            rewrite H
          end.
          apply in_or_app; right; apply in_eq.
        + intuition.
          repeat tuple_inversion.
          eauto.
  Qed.

  Ltac construct_gst_RecvMsg :=
    match goal with
    | [ Hst: sigma ?gst ?d = Some ?st,
        Hmsgs: msgs ?gst = ?xs ++ (?s, (?d, ?p)) :: ?ys
        |- enabled (RecvMsg ?s ?d ?p) ?gst ]=>
      destruct (recv_handler s d st p) as [[[[?st' ?ms] ?nts] ?cts] ?l] eqn:?H;
        remember (apply_handler_result
                    d
                    (st', ms, nts, cts)
                    (e_recv (s, (d, p)))
                    (update_msgs gst (xs ++ ys))) as egst
    end.

  Lemma labeled_step_dynamic_neq_dst_enabled :
    forall gst gst' gst'' dst to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      dst <> to ->
      enabled (RecvMsg src dst m) gst'.
  Proof.
    intuition.
    find_copy_eapply_lem_hyp recv_implies_state_exists; eauto; break_exists.
    find_copy_eapply_lem_hyp recv_implies_msg_in; eauto.
    find_apply_lem_hyp in_split; break_exists.
    construct_gst_RecvMsg.
    exists egst.
    invc_labeled_step.
    - unfold timeout_handler in *; tuple_inversion.
    - invc_labeled_step.
      * unfold timeout_handler in *; tuple_inversion.
      * eapply LDeliver_node;
        eauto;
        unfold apply_handler_result, update_msgs;
        unfold recv_handler in *;
        repeat tuple_inversion;
        eauto.
  Qed.

  Lemma timeout_implies_state_exists :
    forall gst gst' gst'' h t src dst m,
      labeled_step_dynamic gst (Timeout h t) gst'  ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      exists st,
        sigma gst' dst = Some st.
  Proof.
    intuition.
    invc_labeled_step.
    - unfold timeout_handler in *; tuple_inversion.
    - invc_labeled_step.
      * unfold recv_handler in *; repeat tuple_inversion.
        unfold apply_handler_result, update; simpl.
        break_if; eexists; eauto.
      * unfold recv_handler in *; tuple_inversion.
  Qed.

  Lemma recv_implies_message_exists_after_timeout :
    forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    In (src, (dst, m)) (msgs gst').
  Proof.
    intuition.
    invc_labeled_step.
    - unfold timeout_handler in *; tuple_inversion.
    - invc_labeled_step.
      * unfold recv_handler in *; repeat tuple_inversion.
        simpl.
        repeat find_rewrite.
        repeat (apply in_or_app; right).
        unfold fst, snd.
        repeat break_let.
        apply in_eq.
      * unfold recv_handler in *; tuple_inversion.
  Qed.

  Lemma labeled_step_dynamic_timeout_enabled :
    forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    enabled (RecvMsg src dst m) gst'.
  Proof.
    intuition.
    find_copy_eapply_lem_hyp timeout_implies_state_exists; eauto.
    find_copy_eapply_lem_hyp recv_implies_message_exists_after_timeout; eauto.
    find_apply_lem_hyp in_split.
    break_exists.
    construct_gst_RecvMsg.
    exists egst.
    invc_labeled_step.
    - unfold timeout_handler in *; tuple_inversion.
    - invc_labeled_step.
      * eapply LDeliver_node;
        eauto;
        unfold apply_handler_result, update_msgs;
        unfold recv_handler in *;
        repeat tuple_inversion;
        eauto.
      * unfold recv_handler in *; tuple_inversion.
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
         strong_local_fairness s ->
         forall src dst m d, 
           In dst (nodes (occ_gst (hd s))) ->
           ~ In dst (failed_nodes (occ_gst (hd s))) ->
           In (src, (dst, m)) (msgs (occ_gst (hd s))) ->
           sigma (occ_gst (hd s)) dst = Some d ->
           eventually (now (occurred (RecvMsg src dst m))) s.
  Proof.
    move => s H_exec H_fair src dst m d H_in_n H_in_f H_in_m H_s.
    set P := eventually _.
    case (classic (P s)) => //.
    rewrite /P {P} => H_ev.
    suff H_suff: inf_occurred (RecvMsg src dst m) s by inversion H_suff.
    apply: H_fair.
    apply: always_inf_often.
    apply not_eventually_always_not in H_ev.    
    move: H_ev.
    apply: weak_until_always_not_always.
    apply: RecvMsg_enabled_until_occurred => //.
    move: H_s.
    exact: l_enabled_RecvMsg_In_msgs.
  Qed.
End LabeledChord.
