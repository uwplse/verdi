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
    l_enabled (RecvMsg dst src m) e.
  Proof.
  move => e src dst m d H_in_n H_in_f H_in H_s.
  find_apply_lem_hyp in_split.
  break_exists.
  rewrite /l_enabled /enabled.
  case H_r: (recv_handler dst src d m) => [[[[st ms] newts] clearedts] lb].
  have H_lb: lb = RecvMsg dst src m.
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

  Lemma RecvMsg_enabled_until_occurred :
    forall s,
      lb_execution s ->
      forall src dst m,
        l_enabled (RecvMsg dst src m) (hd s) ->
        until (now (l_enabled (RecvMsg dst src m)))
              (now (occurred (RecvMsg dst src m)))
              s.
  Proof.
    cofix c.
    case => /=.
    case => /= gst.
    case => [h from m|h t|].
    - case.
      case => /= gst' lb'.
      (* hard case, use (apply: Until_tl) at some point and then (apply: c) *)
      by admit.
    - case.
      case => /= gst' lb' s H_exec src dst m H_en.
      inversion H_exec; subst_max.
      simpl in *.
      rewrite /l_enabled /= in H_en.
      inversion H1; subst_max => //.
      apply: Until_tl; first by [].
      rewrite /=.
      apply: c; first by [].
      rewrite /= /l_enabled /=.
      rewrite /timeout_handler /= in H5.
      tuple_inversion.
      (* semi-hard case *)
      by admit.
    - case.
      case => /= gst' lb' s H_exec src dst' m H_en.
      inversion H_exec; subst_max.
      simpl in *.
      inversion H1; subst_max => //.      
      apply: Until_tl; first by [].
      exact: c.
   Admitted.

  Lemma RecvMsg_eventually_occurred :
    forall s, lb_execution s ->
         strong_local_fairness s ->
         forall src dst m, l_enabled (RecvMsg dst src m) (hd s) ->
                      eventually (now (occurred (RecvMsg dst src m))) s.
  Proof.
    move => s H_exec H_fair src dst m H_en.
    set P := eventually _.
    case (classic (P s)) => //.
    rewrite /P {P} => H_ev.
    suff H_suff: inf_occurred (RecvMsg dst src m) s by inversion H_suff.
    apply: H_fair.
    apply: always_always_eventually.
    move: H_ev.
    apply: until_not_eventually_always.
    exact: RecvMsg_enabled_until_occurred.
  Qed.

End LabeledChord.
