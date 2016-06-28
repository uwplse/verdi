Require Import Chord.
Require Import LabeledDynamicNet.
Import List.
Require Import infseq.
Require Import infseq_aux.
Require Import StructTact.StructTactics.
Require Import mathcomp.ssreflect.ssreflect.

Require Import Classical. (* yuck *)

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
  | Timeout : addr -> timeout -> label
  | Tau : label.

  Definition label_eq_dec : forall x y : label, {x = y} + {x <> y}.  
  Proof.
    decide equality; eauto using addr_eq_dec, payload_eq_dec, timeout_eq_dec.
  Defined.

  Definition label_silent := Tau.

  Notation occ_gst := (occ_gst addr payload data timeout label).
  Notation occurrence := (occurrence addr payload data timeout label).

  Definition timeout_handler (h : addr) (st : data) (t : timeout) :=
    (timeout_handler hash h st t, Timeout h t).

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) :=
    (recv_handler SUCC_LIST_LEN hash src dst st msg, RecvMsg src dst msg).

  (* todo *)
  Variable extra_constraints : gpred addr payload data timeout.
  Variable extra_constraints_all : forall gpred, extra_constraints gpred.

  Notation labeled_step_dynamic := (labeled_step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation lb_execution := (lb_execution addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation strong_local_fairness := (strong_local_fairness addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation inf_occurred := (inf_occurred addr payload data timeout label).
  Notation enabled := (enabled addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation l_enabled := (l_enabled addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
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
  have H_fst_snd: dst = fst (snd (src, (dst, m))) by [].
  have H_snd_snd: m = snd (snd (src, (dst, m))) by [].
  rewrite H_snd_snd {H_snd_snd} in H_r.
  have H_fst: src = fst (src, (dst, m)) by [].
  rewrite H_fst {H_fst} in H_r.
  have H_gst': gst' = gst' by [].
  rewrite {2}/gst' in H_gst'.
  have H_p: extra_constraints gst' by [].
  move: H_r H_gst' H_p.  
  exact: LDeliver_node.
  Qed.

  Lemma labeled_step_dynamic_neq_payload_enabled :
    forall gst gst' gst'' to from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg from to m) gst'' ->
      m <> p ->
      enabled (RecvMsg from to m) gst'.
  Proof.
  Admitted.

  Lemma labeled_step_dynamic_neq_src_enabled :
    forall gst gst' gst'' to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src to m) gst'' ->
      src <> from ->
      enabled (RecvMsg src to m) gst'.
  Proof.
  Admitted.

  Lemma labeled_step_dynamic_neq_dst_enabled :
    forall gst gst' gst'' dst to src from m p,
      labeled_step_dynamic gst (RecvMsg from to p) gst' ->
      labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
      dst <> to -> 
      enabled (RecvMsg src dst m) gst'.
  Proof.
  Admitted.

  Lemma labeled_step_dynamic_timeout_enabled :
    forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    enabled (RecvMsg src dst m) gst'.
  Proof.
  Admitted.

  Lemma RecvMsg_enabled_until_occurred :
    forall s, lb_execution s ->
      forall src dst m, l_enabled (RecvMsg src dst m) (hd s) ->
        until (now (l_enabled (RecvMsg src dst m)))
              (now (occurred (RecvMsg src dst m)))
              s.
  Proof.
    cofix c.
    case => /=.
    case => /= gst.
    case => [from to p|h t|].
    - case.
      case => /= gst' lb' s H_exec src dst m H_en.
      inversion H_exec; subst_max.
      simpl in *.
      case (addr_eq_dec dst to) => H_dec_dst.
        case (addr_eq_dec src from) => H_dec_src.
          case (payload_eq_dec m p) => H_dec_m.
            subst_max.
            exact: Until0.
          subst_max.
          apply: Until_tl; first by [].
          apply: c => //=.
          unfold l_enabled in *.
          simpl in *.
          unfold enabled in H_en.
          break_exists.
          move: H1 H H_dec_m.
          exact: labeled_step_dynamic_neq_payload_enabled.
        subst_max.
        apply: Until_tl; first by [].
        apply: c => //=.
        unfold l_enabled in *.
        simpl in *.
        unfold enabled in H_en.
        break_exists.
        move: H1 H H_dec_src.
        exact: labeled_step_dynamic_neq_src_enabled.
      apply: Until_tl; first by [].
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
      apply: Until_tl; first by [].
      apply: c => //=.
      unfold l_enabled in *.
      simpl in *.
      unfold enabled in H_en.
      break_exists.
      move: H1 H.
      exact: labeled_step_dynamic_timeout_enabled.
    - case.
      case => /= gst' lb' s H_exec src dst' m H_en.
      inversion H_exec; subst_max.
      simpl in *.
      inversion H1; subst_max => //.      
      apply: Until_tl; first by [].
      exact: c.
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
    apply: always_always_eventually.
    move: H_ev.
    apply: until_not_eventually_always.
    apply: RecvMsg_enabled_until_occurred => //.
    move: H_s.
    exact: l_enabled_RecvMsg_In_msgs.
  Qed.
End LabeledChord.
