Require Import Verdi.Verdi.
Require Import Verdi.LabeledNet.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.TotalMapExecutionSimulations.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.map.
Require Import InfSeqExt.exteq.

Require Import FunctionalExtensionality.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Set Implicit Arguments.

Class LabeledMultiParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1)
  (B : BaseParamsPartialMap B0 B1) 
  (N : MultiParamsNameTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (P : MultiParamsMsgPartialMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (L : LabeledMultiParamsLabelTotalMap P0 P1) : Prop :=
  {
    pt_lb_label_silent_fst_snd : tot_map_label label_silent = label_silent ;
    pt_lb_net_handlers_some : forall me src m st m' out st' ps lb,
      pt_map_msg m = Some m' ->
      lb_net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) = (lb, out, st', ps) ->
      lb <> label_silent /\ tot_mapped_lb_net_handlers_label me src m st = lb ;
    pt_lb_net_handlers_none : forall me src m st,
      pt_map_msg m = None ->
      tot_mapped_lb_net_handlers_label me src m st = label_silent ;
    pt_lb_input_handlers_some : forall me inp st inp' out st' ps lb,
      pt_map_input inp = Some inp' ->
      lb_input_handlers (tot_map_name me) inp' (pt_map_data st) = (lb, out, st', ps) ->
      lb <> label_silent /\ tot_mapped_lb_input_handlers_label me inp st = lb ;
    pt_lb_input_handlers_none : forall me inp st,
      pt_map_input inp = None ->
      tot_mapped_lb_input_handlers_label me inp st = label_silent
  }.

Section PartialMapExecutionSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {msg_map : MultiParamsMsgPartialMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map msg_map}.
Context {multi_map_lb_congr : LabeledMultiParamsPartialMapCongruency base_map name_map msg_map label_map}.

Hypothesis label_eq_dec : forall x y : label, {x = y} + {x <> y}.

Hypothesis tot_map_label_injective : 
  forall l l', tot_map_label l = tot_map_label l' -> l = l'.

Hypothesis label_tot_mapped :
  forall l, exists l', l = tot_map_label l'.

(* lb_step_failure *)

Theorem lb_step_failure_pt_mapped_simulation_1_non_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb <> label_silent ->
    @lb_step_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_net net) (tot_map_label lb) (List.map tot_map_name failed', pt_map_net net') (pt_map_trace tr).
Proof.
move => net net' failed failed' lb tr H_neq H_step.
have H_neq': lb <> label_silent.
  rewrite -pt_lb_label_silent_fst_snd in H_neq.
  move => H_eq.
  by rewrite H_eq in H_neq.
invcs H_step => //=.
- case H_m: (pt_map_packet p) => [p'|]; last first.
    destruct p.
    simpl in *.
    break_match => //.
    have H_q := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr pDst pSrc _ (nwState net pDst) Heqo.
    rewrite /tot_mapped_lb_net_handlers_label in H_q.
    repeat break_let.
    by tuple_inversion.
  have H_eq_n: tot_map_name (pDst p) = pDst p'.
    destruct p.
    simpl in *.
    break_match => //.
    by find_injection.
  rewrite H_eq_n.
  apply (@LabeledStepFailure_deliver _ _ _ _ _ _ (pt_map_packets xs) (pt_map_packets ys) (pt_map_outputs out) (pt_map_data d) (@pt_map_name_msgs _ _ _ _ _ msg_map l)).
  * rewrite /pt_map_net /=.
    find_rewrite.
    by rewrite pt_map_packets_app_distr /= H_m.
  * rewrite -H_eq_n.
    exact: not_in_failed_not_in.
  * rewrite /pt_map_net /= -{2}H_eq_n tot_map_name_inv_inverse.
    destruct p, p'.
    simpl in *.
    break_match => //.
    find_injection.
    clean.
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) _ Heqo.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ Heqo Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    break_and.
    by repeat tuple_inversion.
  * rewrite /pt_map_net /= 2!pt_map_packets_app_distr.
    by rewrite (pt_map_packet_map_eq_some _ _ H_m) (pt_map_update_eq_some _ _ _ H_m).
- case H_i: pt_map_input => [inp'|]; last first.
    have H_q := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ (nwState net h) H_i.
    rewrite /tot_mapped_lb_input_handlers_label /= in H_q.
    repeat break_let.
    by tuple_inversion.
  apply (@LabeledStepFailure_input _ _ _ _ _ _ _ _ (pt_map_data d) (@pt_map_name_msgs _ _ _ _ _ msg_map l)).
  * exact: not_in_failed_not_in.
  * have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    break_and.
    unfold tot_mapped_lb_input_handlers_label in *.
    repeat break_let.
    repeat tuple_inversion.
    by rewrite /pt_map_net /= tot_map_name_inv_inverse.
  * rewrite /pt_map_net /=.
    rewrite pt_map_packets_app_distr pt_map_packet_map_eq.
    by rewrite -(@pt_map_update_eq  _ _ _ _ _ _ name_map_bijective).
Qed.

Theorem lb_step_failure_pt_mapped_simulation_1_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb = label_silent ->
    @lb_step_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_net net) label_silent (List.map tot_map_name failed', pt_map_net net') [] /\ pt_trace_remove_empty_out (pt_map_trace tr) = [].
Proof.
move => net net' failed failed' lb tr H_eq H_step.
invcs H_step => //=.
- case H_m: (pt_map_packet p) => [p'|].
    destruct p, p'.
    simpl in *.
    break_match_hyp => //.
    find_injection.
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) _ Heqo.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ Heqo Heqp1.
    break_and.
    unfold tot_mapped_lb_net_handlers_label in *.
    repeat break_let.
    by repeat tuple_inversion.
  destruct p.
  simpl in *.
  break_match_hyp => //.
  have H_q := @pt_net_handlers_none _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) out d l Heqo.
  rewrite /net_handlers /= /unlabeled_net_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr pDst pSrc _ (nwState net pDst) Heqo.
  rewrite /tot_mapped_lb_net_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_net /=.
  rewrite pt_map_packets_app_distr.
  rewrite pt_map_name_msgs_empty_eq //=.
  rewrite H3.
  rewrite pt_map_packets_app_distr /=.
  repeat break_match => //.
  rewrite -pt_map_packets_app_distr.
  set s1 := fun _ => _.
  set s2 := fun _ => _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2.
    apply functional_extensionality => n.
    rewrite /update.
    by break_if; first by rewrite H e.
  rewrite -H_eq_s /s1 {s1 s2 H_eq_s}.
  split => //.
  exact: LabeledStepFailure_stutter.
- case H_i: (pt_map_input inp) => [inp'|].
    have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    break_and.
    unfold tot_mapped_lb_input_handlers_label in *.
    repeat break_let.
    by tuple_inversion.
  have H_q := @pt_input_handlers_none _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) out d l H_i.
  rewrite /input_handlers /= /unlabeled_input_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ (nwState net h) H_i.
  rewrite /tot_mapped_lb_input_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_net /=.
  rewrite pt_map_packets_app_distr.
  rewrite pt_map_name_msgs_empty_eq //=.
  set s1 := fun _ => _.
  set s2 := fun _ => _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2.
    apply functional_extensionality => n.
    rewrite /update.
    by break_if; first by rewrite H e.
  rewrite -H_eq_s /s1 {s1 s2 H_eq_s}.
  split; first exact: LabeledStepFailure_stutter.
  by repeat find_rewrite.
- split => //; exact: LabeledStepFailure_stutter.
Qed.

(* lb_step_ordered_failure *)

Theorem lb_step_ordered_failure_pt_mapped_simulation_1_non_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb <> label_silent ->
    @lb_step_ordered_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_ordered_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_onet net) (tot_map_label lb) (List.map tot_map_name failed', pt_map_onet net') (pt_map_traces tr).
Proof.
move => net net' failed failed' lb tr H_neq H_step.
have H_neq': lb <> label_silent.
  rewrite -pt_lb_label_silent_fst_snd in H_neq.
  move => H_eq.
  by rewrite H_eq in H_neq.
invcs H_step => //=.
- rewrite {2}/pt_map_onet /=.
  case H_m: (@pt_map_msg _ _ _ _ msg_map m) => [m'|]; last first.
    have H_q := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr to from _ (onwState net to) H_m.
    rewrite /tot_mapped_lb_net_handlers_label in H_q.
    repeat break_let.
    by tuple_inversion.
  apply (@LabeledStepOrderedFailure_deliver _ _ _ _ _ _ m' (@pt_map_msgs _ _ _ _ msg_map ms) (pt_map_outputs out) (pt_map_data d) (@pt_map_name_msgs _ _ _ _ _ msg_map l) (@tot_map_name _ _ _ _ name_map from) (@tot_map_name _ _ _ _ name_map to)).
  * by rewrite /= 2!tot_map_name_inv_inverse /= H3 /= H_m.
  * exact: not_in_failed_not_in.
  * rewrite /pt_map_onet /= tot_map_name_inv_inverse.
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr to from m (onwState net to) _ H_m.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ H_m Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    break_and.
    by repeat tuple_inversion.
  * rewrite (@collate_pt_map_update2_eq _ _ _ _ name_map).
    set f1 := fun _ => pt_map_data _.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2.
      apply functional_extensionality => n.
      rewrite /update.
      break_if; break_if => //=; first by rewrite -e tot_map_name_inverse_inv in n0.
      by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite pt_map_traces_outputs_eq.
- rewrite {2}/pt_map_onet /=.
  case H_i: pt_map_input => [inp'|]; last first.
    have H_q := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h inp (onwState net h) H_i.
    rewrite /tot_mapped_lb_input_handlers_label in H_q.
    repeat break_let.
    by tuple_inversion.
  apply (@LabeledStepOrderedFailure_input _ _ (@tot_map_name _ _ _ _ name_map h) _ _ _ _ (pt_map_outputs out) inp' (pt_map_data d) (@pt_map_name_msgs _ _ _ _ _ msg_map l)).
  * exact: not_in_failed_not_in.
  * rewrite /pt_map_onet /= tot_map_name_inv_inverse.
    have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h inp (onwState net h) _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    rewrite /tot_mapped_lb_input_handlers_label in H_q'.
    repeat break_let.
    break_and.
    by repeat tuple_inversion.
  * rewrite {2}/pt_map_onet /=.
    rewrite (@collate_pt_map_eq _ _ _ _ name_map).
    set f1 := fun _ => pt_map_data _.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2.
      apply functional_extensionality => n.
      rewrite /update.
      break_if; break_if => //=; first by rewrite -e tot_map_name_inverse_inv in n0.
      by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite pt_map_traces_outputs_eq.
Qed.
     
Theorem lb_step_ordered_failure_pt_mapped_simulation_1_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb = label_silent ->
    @lb_step_ordered_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_ordered_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_onet net) label_silent (List.map tot_map_name failed', pt_map_onet net') [] /\ pt_map_traces tr = [].
Proof.
move => net net' failed failed' lb tr H_eq H_step.
invcs H_step => //=.
- rewrite {2}/pt_map_onet /=.
  case H_m: (@pt_map_msg _ _ _ _ msg_map m) => [m'|].
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr to from m (onwState net to) _ H_m.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ H_m Heqp1.
    break_and.
    unfold tot_mapped_lb_net_handlers_label in *.
    repeat break_let.
    by repeat tuple_inversion.
  have H_q := @pt_net_handlers_none _ _ _ _ _ _ _ multi_map_congr to from m (onwState net to) out d l H_m.
  rewrite /net_handlers /= /unlabeled_net_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr to from _ (onwState net to) H_m.
  rewrite /tot_mapped_lb_net_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_onet /=.
  rewrite (@collate_pt_map_update2_eq _ _ _ _ name_map) /=.
  rewrite H0 /=.
  set p1 := fun _ _ => _.
  set p2 := update2 _ _ _ _ _.
  set s1 := fun _ => _.
  set s2 := fun _ => _.
  have H_eq_p: p1 = p2.
    rewrite /p1 /p2 /update2.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    break_if => //.
    break_and.
    by rewrite -H2 -H5 2!tot_map_name_inv_inverse H3 /= H_m.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2 /update.
    apply functional_extensionality => n.
    break_if => //.
    by rewrite H e.
  rewrite H_eq_p H_eq_s.
  split; first exact: LabeledStepOrderedFailure_stutter.
  rewrite pt_map_traces_outputs_eq.
  by repeat find_rewrite.
- case H_i: (pt_map_input inp) => [inp'|].
    have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ (onwState net h) _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    break_and.
    unfold tot_mapped_lb_input_handlers_label in *.
    repeat break_let.
    by tuple_inversion.
  have H_q := @pt_input_handlers_none _ _ _ _ _ _ _ multi_map_congr h _ (onwState net h) out d l H_i.
  rewrite /input_handlers /= /unlabeled_input_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ (onwState net h) H_i.
  rewrite /tot_mapped_lb_input_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_onet /=.
  rewrite (@collate_pt_map_eq _ _ _ _ name_map) H0 /=.
  set s1 := fun _ => pt_map_data _.
  set s2 := fun _ => pt_map_data _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2.
    apply functional_extensionality => n.
    rewrite /update.
    by break_if; first by rewrite H e.
  rewrite -H_eq_s /s1 {s1 s2 H_eq_s}.
  split; first exact: LabeledStepOrderedFailure_stutter.
  rewrite pt_map_traces_outputs_eq.
  by repeat find_rewrite.
- split => //; exact: LabeledStepOrderedFailure_stutter.
Qed.

Definition pt_map_onet_event e :=
{| evt_a := (List.map tot_map_name (fst e.(evt_a)), pt_map_onet (snd e.(evt_a))) ;
   evt_l := tot_map_label e.(evt_l) ;
   evt_trace := pt_map_traces e.(evt_trace) |}.

Lemma pt_map_onet_event_Map_unfold : forall s,
 Cons (pt_map_onet_event (hd s)) (map pt_map_onet_event (tl s)) = map pt_map_onet_event s.
Proof.
by move => s; rewrite -map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_execution_lb_step_ordered_failure_pt_map_onet_infseq : forall s,
  lb_step_execution lb_step_ordered_failure s ->
  lb_step_execution lb_step_ordered_failure (map pt_map_onet_event s).
Proof.
cofix c.
move => s H_exec.
rewrite -pt_map_onet_event_Map_unfold {1}/pt_map_onet_event /=.
inversion H_exec; subst => /=.
rewrite -pt_map_onet_event_Map_unfold /= /pt_map_onet_event /=.
case (label_eq_dec (tot_map_label (evt_l e)) label_silent) => H_eq.
  apply: Cons_lb_step_exec.
  - rewrite H_eq.
    destruct e, e'.
    destruct evt_a, evt_a0.
    simpl in *.
    by eapply lb_step_ordered_failure_pt_mapped_simulation_1_silent; eauto.
  - destruct e, e'.
    destruct evt_a, evt_a0.
    apply (lb_step_ordered_failure_pt_mapped_simulation_1_silent H_eq) in H.
    break_and.
    simpl in *.
    rewrite H0 pt_map_traces_app.
    by aggressive_rewrite_goal.
  - pose s' := Cons e' s0.
    rewrite (pt_map_onet_event_Map_unfold s').
    exact: c.
apply: Cons_lb_step_exec => /=.
- destruct e, e'.
  destruct evt_a, evt_a0.
  simpl in *.
  by eapply lb_step_ordered_failure_pt_mapped_simulation_1_non_silent; eauto.
- by rewrite H0 pt_map_traces_app.
- pose s' := Cons e' s0.
  rewrite (pt_map_onet_event_Map_unfold s').
  exact: c.
Qed.

Lemma pt_map_onet_tot_map_label_event_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (map pt_map_onet_event s).
Proof.
move => l.
apply: always_map.
apply: eventually_map.
case => e s.
rewrite /= /occurred /evt_l /=.
move => H_eq.
by rewrite H_eq.
Qed.

Lemma pt_map_onet_tot_map_label_event_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (map pt_map_onet_event s) ->
    inf_often (now (occurred l)) s.
Proof.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
- exact: extensional_now.
- exact: extensional_now.
- case => e s.
  rewrite /= /occurred /=.
  move => H_eq.
  exact: tot_map_label_injective.
Qed.

Hypothesis lb_step_ordered_failure_strong_fairness_enabled_pt_map_onet_eventually :
  forall l, tot_map_label l <> label_silent ->
    forall s, lb_step_execution lb_step_ordered_failure s ->
    strong_local_fairness lb_step_ordered_failure label_silent s ->        
    l_enabled lb_step_ordered_failure (tot_map_label l) (pt_map_onet_event (hd s)) ->
    eventually (now (l_enabled lb_step_ordered_failure l)) s.

Lemma pt_map_onet_tot_map_labeled_event_inf_often_enabled :
  forall l, tot_map_label l <> label_silent ->
    forall s, lb_step_execution lb_step_ordered_failure s ->
    strong_local_fairness lb_step_ordered_failure label_silent s ->
    inf_often (now (l_enabled lb_step_ordered_failure (tot_map_label l))) (map pt_map_onet_event s) ->
    inf_often (now (l_enabled lb_step_ordered_failure l)) s.
Proof.
move => l H_neq s H_exec H_fair.
have H_a: ((lb_step_execution lb_step_ordered_failure) /\_ (strong_local_fairness lb_step_ordered_failure label_silent)) s by auto.
move: H_a {H_exec H_fair}.
apply: always_map_conv_ext => {s}.
  rewrite /and_tl /=.
  move => x s0 [H_e H_w].
  apply lb_step_execution_invar in H_e.
  by apply strong_local_fairness_invar in H_w.
apply: eventually_map_conv_ext.
- exact: extensional_now.
- exact: extensional_now.
- apply extensional_and_tl.
  * exact: lb_step_execution_extensional.
  * exact: strong_local_fairness_extensional.
- rewrite /and_tl /=.
  move => x s [H_e H_w].
  apply lb_step_execution_invar in H_e.
  by apply strong_local_fairness_invar in H_w.
- rewrite /and_tl.
  case => /= x s [H_a H_w] H_en.
  exact: lb_step_ordered_failure_strong_fairness_enabled_pt_map_onet_eventually.
Qed.

Hypothesis lb_step_ordered_failure_weak_fairness_always_enabled_pt_map_onet_continuously : 
  forall l, tot_map_label l <> label_silent -> 
    forall s, lb_step_execution lb_step_ordered_failure s ->
    weak_local_fairness lb_step_ordered_failure label_silent s ->
    always (now (l_enabled lb_step_ordered_failure (tot_map_label l))) (map pt_map_onet_event s) ->
    continuously (now (l_enabled lb_step_ordered_failure l)) s.

Lemma pt_map_onet_tot_map_labeled_event_state_continuously_enabled :
  forall l, tot_map_label l <> label_silent ->    
    forall s, lb_step_execution lb_step_ordered_failure s ->
    weak_local_fairness lb_step_ordered_failure label_silent s ->
    continuously (now (l_enabled lb_step_ordered_failure (tot_map_label l))) (map pt_map_onet_event s) ->
    continuously (now (l_enabled lb_step_ordered_failure l)) s.
Proof.
move => l H_neq s H_exec H_fair.
have H_a: ((lb_step_execution lb_step_ordered_failure) /\_ (weak_local_fairness lb_step_ordered_failure label_silent)) s by auto.
move: H_a {H_exec H_fair}.
apply: eventually_map_conv_ext => {s}.
- apply extensional_always.
  exact: extensional_now.
- apply extensional_always.
  exact: extensional_now.
- apply extensional_and_tl.
  * exact: lb_step_execution_extensional.
  * exact: weak_local_fairness_extensional.
- rewrite /and_tl /=.
  move => x s [H_e H_w].
  apply lb_step_execution_invar in H_e.
  by apply weak_local_fairness_invar in H_w.
- case => x s [H_a H_w] H_al.
  simpl in *.
  exact: lb_step_ordered_failure_weak_fairness_always_enabled_pt_map_onet_continuously.
Qed.

Lemma pt_map_onet_tot_map_label_event_strong_local_fairness : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       strong_local_fairness lb_step_ordered_failure label_silent s ->
       strong_local_fairness lb_step_ordered_failure label_silent (map pt_map_onet_event s).
Proof.
move => s.
rewrite /strong_local_fairness => H_exec H_fair l H_neq H_en.
have [l' H_l] := label_tot_mapped l.
rewrite H_l.
apply pt_map_onet_tot_map_label_event_inf_often_occurred.
apply H_fair; first by move => H_eq; rewrite H_eq pt_lb_label_silent_fst_snd in H_l.
rewrite H_l in H_en.
unfold inf_enabled in *.
apply: pt_map_onet_tot_map_labeled_event_inf_often_enabled => //.
move => H_eq.
by rewrite -H_l in H_eq.
Qed.

Lemma pt_map_onet_tot_map_label_event_state_weak_local_fairness : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       weak_local_fairness lb_step_ordered_failure label_silent (map pt_map_onet_event s).
Proof.
move => s.
rewrite /weak_local_fairness => H_exec H_fair l H_neq H_en.
have [l' H_l] := label_tot_mapped l.
rewrite H_l.
apply pt_map_onet_tot_map_label_event_inf_often_occurred.
apply H_fair; first by move => H_eq; rewrite H_eq pt_lb_label_silent_fst_snd in H_l.
rewrite H_l in H_en.
unfold cont_enabled in *.
apply: pt_map_onet_tot_map_labeled_event_state_continuously_enabled => //.
move => H_eq.
by rewrite -H_l in H_eq.
Qed.

Context {overlay_fst : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {overlay_snd : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Context {fail_msg_fst : FailMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_msg_snd : FailMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd msg_map}.

Lemma pt_map_onet_hd_step_ordered_failure_star : 
  forall e, event_step_star step_ordered_failure step_ordered_failure_init e ->
       event_step_star step_ordered_failure step_ordered_failure_init (pt_map_onet_event e).
Proof.
move => e.
rewrite /= /pt_map_onet_event /= /event_step_star /=.
move => H_star.
destruct e, evt_a.
simpl in *.
exact: step_ordered_failure_pt_mapped_simulation_star_1.
Qed.

Lemma pt_map_onet_hd_step_ordered_failure_star_always : 
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       always (now (event_step_star step_ordered_failure step_ordered_failure_init)) (map pt_map_onet_event s).
Proof.
case => e s H_star H_exec.
apply: step_ordered_failure_star_lb_step_execution; first exact: pt_map_onet_hd_step_ordered_failure_star.
exact: lb_step_execution_lb_step_ordered_failure_pt_map_onet_infseq.
Qed.

(* lb_step_ordered_dynamic_failure *)

Theorem lb_step_ordered_dynamic_failure_pt_mapped_simulation_1_non_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb <> label_silent ->
    @lb_step_ordered_dynamic_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_ordered_dynamic_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_odnet net) (tot_map_label lb) (List.map tot_map_name failed', pt_map_odnet net') (pt_map_traces tr).
Proof.
move => net net' failed failed' lb tr H_neq H_step.
have H_neq': lb <> label_silent.
  rewrite -pt_lb_label_silent_fst_snd in H_neq.
  move => H_eq.
  by rewrite H_eq in H_neq.
invcs H_step => //=.
- rewrite {2}/pt_map_odnet /=.
  case H_m: (@pt_map_msg _ _ _ _ msg_map m) => [m'|]; last first.
    have H_q := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr to from _ d H_m.
    rewrite /tot_mapped_lb_net_handlers_label in H_q.
    repeat break_let.
    by tuple_inversion.
  apply (@LabeledStepOrderedDynamicFailure_deliver _ _ _ _ _ _ m' (@pt_map_msgs _ _ _ _ msg_map ms) (pt_map_outputs out) (pt_map_data d) (pt_map_data d') (@pt_map_name_msgs _ _ _ _ _ msg_map l) (@tot_map_name _ _ _ _ name_map from) (@tot_map_name _ _ _ _ name_map to)).
  * exact: not_in_failed_not_in.
  * exact: in_failed_in. 
  * by rewrite /pt_map_odnet /= tot_map_name_inv_inverse H5.
  * by rewrite /pt_map_odnet /= 2!tot_map_name_inv_inverse H6 /= H_m.
  * have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr to from m d _ H_m.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ H_m Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    break_and.
    by repeat tuple_inversion.
  * rewrite {2}/pt_map_odnet /=.
    rewrite (@collate_pt_map_update2_eq _ _ _ _ name_map).
    set f1 := fun _ => match _ with _ => _ end.    
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2.
      apply functional_extensionality => n.
      rewrite /update.
      break_if; break_if => //=; first by rewrite -e tot_map_name_inverse_inv in n0.
      by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite pt_map_traces_outputs_eq.
- rewrite {2}/pt_map_odnet /=.
  case H_i: pt_map_input => [inp'|]; last first.
    have H_q := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h inp d H_i.
    rewrite /tot_mapped_lb_input_handlers_label in H_q.
    repeat break_let.
    by tuple_inversion.
  apply (@LabeledStepOrderedDynamicFailure_input _ _ (@tot_map_name _ _ _ _ name_map h) _ _ _ _ (pt_map_outputs out) inp' (pt_map_data d) (pt_map_data d') (@pt_map_name_msgs _ _ _ _ _ msg_map l)).
  * exact: not_in_failed_not_in.
  * exact: in_failed_in.
  * by rewrite /pt_map_odnet /= tot_map_name_inv_inverse H5.
  * have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h inp d _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    rewrite /tot_mapped_lb_input_handlers_label in H_q'.
    repeat break_let.
    break_and.
    by repeat tuple_inversion.
  * rewrite {2}/pt_map_odnet /=.
    rewrite (@collate_pt_map_eq _ _ _ _ name_map).
    set f1 := fun _ => match _ with _ => _ end.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2.
      apply functional_extensionality => n.
      rewrite /update.
      break_if; break_if => //=; first by rewrite -e tot_map_name_inverse_inv in n0.
      by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite pt_map_traces_outputs_eq.
Qed.

Theorem lb_step_ordered_dynamic_failure_pt_mapped_simulation_1_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb = label_silent ->
    @lb_step_ordered_dynamic_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_ordered_dynamic_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_odnet net) label_silent (List.map tot_map_name failed', pt_map_odnet net') [] /\ pt_map_traces tr = [].
Proof.
move => net net' failed failed' lb tr H_eq H_step.
invcs H_step => //=.
- rewrite {2}/pt_map_odnet /=.
  case H_m: (@pt_map_msg _ _ _ _ msg_map m) => [m'|].
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr to from m d _ H_m.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ H_m Heqp1.
    break_and.
    unfold tot_mapped_lb_net_handlers_label in *.
    repeat break_let.
    by repeat tuple_inversion.
  have H_q := @pt_net_handlers_none _ _ _ _ _ _ _ multi_map_congr to from m d out d' l H_m.
  rewrite /net_handlers /= /unlabeled_net_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr to from _ d H_m.
  rewrite /tot_mapped_lb_net_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_odnet /=.
  rewrite (@collate_pt_map_update2_eq _ _ _ _ name_map) /=.
  rewrite H0 /=.
  set p1 := fun _ _ => _.
  set p2 := update2 _ _ _ _ _.
  set s1 := fun _ => _.
  set s2 := fun _ => _.
  have H_eq_p: p1 = p2.
    rewrite /p1 /p2 /update2.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    break_if => //.
    break_and.
    by rewrite -H2 -H7 2!tot_map_name_inv_inverse H6 /= H_m.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2 /update.
    apply functional_extensionality => n.
    break_if => //.
    by rewrite e H5 H.
  rewrite H_eq_p H_eq_s.
  split; first exact: LabeledStepOrderedDynamicFailure_stutter.
  rewrite pt_map_traces_outputs_eq.
  by repeat find_rewrite.
- case H_i: (pt_map_input inp) => [inp'|].
    have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ d _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    break_and.
    unfold tot_mapped_lb_input_handlers_label in *.
    repeat break_let.
    by tuple_inversion.
  have H_q := @pt_input_handlers_none _ _ _ _ _ _ _ multi_map_congr h _ d out d' l H_i.
  rewrite /input_handlers /= /unlabeled_input_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ d H_i.
  rewrite /tot_mapped_lb_input_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_odnet /=.
  rewrite (@collate_pt_map_eq _ _ _ _ name_map) H0 /=.
  set s1 := fun _ => match _ with _ => _ end.
  set s2 := fun _ => match _ with _ => _ end.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2.
    apply functional_extensionality => n.
    rewrite /update.
    by break_if; first by rewrite e H5 H.
  rewrite -H_eq_s /s1 {s1 s2 H_eq_s}.
  split; first exact: LabeledStepOrderedDynamicFailure_stutter.
  rewrite pt_map_traces_outputs_eq.
  by repeat find_rewrite.
- split => //; exact: LabeledStepOrderedDynamicFailure_stutter.
Qed.

Definition pt_map_odnet_event e :=
{| evt_a := (List.map tot_map_name (fst e.(evt_a)), pt_map_odnet (snd e.(evt_a))) ;
   evt_l := tot_map_label e.(evt_l) ;
   evt_trace := pt_map_traces e.(evt_trace) |}.

Lemma pt_map_odnet_event_Map_unfold : forall s,
 Cons (pt_map_odnet_event (hd s)) (map pt_map_odnet_event (tl s)) = map pt_map_odnet_event s.
Proof.
by move => s; rewrite -map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_execution_lb_step_ordered_dynamic_failure_pt_map_odnet_infseq : forall s,
  lb_step_execution lb_step_ordered_dynamic_failure s ->
  lb_step_execution lb_step_ordered_dynamic_failure (map pt_map_odnet_event s).
Proof.
cofix c.
move => s H_exec.
rewrite -pt_map_odnet_event_Map_unfold {1}/pt_map_odnet_event /=.
inversion H_exec; subst => /=.
rewrite -pt_map_odnet_event_Map_unfold /= /pt_map_odnet_event /=.
case (label_eq_dec (tot_map_label (evt_l e)) label_silent) => H_eq.
  apply: Cons_lb_step_exec => /=.
  - rewrite H_eq.
    destruct e, e'.
    destruct evt_a, evt_a0.
    simpl in *.
    by eapply lb_step_ordered_dynamic_failure_pt_mapped_simulation_1_silent; eauto.
  - destruct e, e'.
    destruct evt_a, evt_a0.
    simpl in *.
    apply (lb_step_ordered_dynamic_failure_pt_mapped_simulation_1_silent H_eq) in H.
    break_and.
    simpl in *.
    rewrite H0 pt_map_traces_app.
    by aggressive_rewrite_goal.
  - pose s' := Cons e' s0.
    rewrite (pt_map_odnet_event_Map_unfold s').
    exact: c.
apply: Cons_lb_step_exec => /=.
- destruct e, e'.
  destruct evt_a, evt_a0.
  simpl in *.
  by eapply lb_step_ordered_dynamic_failure_pt_mapped_simulation_1_non_silent; eauto.
- by rewrite H0 pt_map_traces_app.
- pose s' := Cons e' s0.
  rewrite (pt_map_odnet_event_Map_unfold s').
  exact: c.
Qed.

Lemma pt_map_odnet_tot_map_label_event_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (map pt_map_odnet_event s).
Proof.
move => l.
apply: always_map.
apply: eventually_map.
case => e s.
rewrite /= /occurred /evt_l /=.
move => H_eq.
by rewrite H_eq.
Qed.

Lemma pt_map_odnet_tot_map_label_event_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (map pt_map_odnet_event s) ->
    inf_often (now (occurred l)) s.
Proof.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
- exact: extensional_now.
- exact: extensional_now.
- case => e s.
  rewrite /= /occurred /=.
  move => H_eq.
  exact: tot_map_label_injective.
Qed.

Hypothesis lb_step_ordered_dynamic_failure_strong_fairness_enabled_pt_map_onet_eventually :
  forall l, tot_map_label l <> label_silent ->
    forall s, lb_step_execution lb_step_ordered_dynamic_failure s ->
    strong_local_fairness lb_step_ordered_dynamic_failure label_silent s ->
    l_enabled lb_step_ordered_dynamic_failure (tot_map_label l) (pt_map_odnet_event (hd s)) ->
    eventually (now (l_enabled lb_step_ordered_dynamic_failure l)) s.

Lemma pt_map_odnet_tot_map_labeled_event_inf_often_enabled :
  forall l, tot_map_label l <> label_silent ->
    forall s, lb_step_execution lb_step_ordered_dynamic_failure s ->
    strong_local_fairness lb_step_ordered_dynamic_failure label_silent s ->
    inf_often (now (l_enabled lb_step_ordered_dynamic_failure (tot_map_label l))) (map pt_map_odnet_event s) ->
    inf_often (now (l_enabled lb_step_ordered_dynamic_failure l)) s.
Proof.
move => l H_neq s H_exec H_fair.
have H_a: ((lb_step_execution lb_step_ordered_dynamic_failure) /\_ (strong_local_fairness lb_step_ordered_dynamic_failure label_silent)) s by auto.
move: H_a {H_exec H_fair}.
apply: always_map_conv_ext => {s}.
  rewrite /and_tl /=.
  move => x s0 [H_e H_w].
  apply lb_step_execution_invar in H_e.
  by apply strong_local_fairness_invar in H_w.
apply: eventually_map_conv_ext.
- exact: extensional_now.
- exact: extensional_now.
- apply extensional_and_tl.
  * exact: lb_step_execution_extensional.
  * exact: strong_local_fairness_extensional.
- rewrite /and_tl /=.
  move => x s [H_e H_w].
  apply lb_step_execution_invar in H_e.
  by apply strong_local_fairness_invar in H_w.
- rewrite /and_tl.
  case => /= x s [H_a H_w] H_en.
  exact: lb_step_ordered_dynamic_failure_strong_fairness_enabled_pt_map_onet_eventually.
Qed.

Hypothesis lb_step_ordered_dynamic_failure_weak_fairness_always_enabled_pt_map_onet_continuously : 
  forall l, tot_map_label l <> label_silent -> 
    forall s, lb_step_execution lb_step_ordered_dynamic_failure s ->
    weak_local_fairness lb_step_ordered_dynamic_failure label_silent s ->
    always (now (l_enabled lb_step_ordered_dynamic_failure (tot_map_label l))) (map pt_map_odnet_event s) ->
    continuously (now (l_enabled lb_step_ordered_dynamic_failure l)) s.

Lemma pt_map_odnet_tot_map_labeled_event_state_continuously_enabled :
  forall l, tot_map_label l <> label_silent ->    
    forall s, lb_step_execution lb_step_ordered_dynamic_failure s ->
    weak_local_fairness lb_step_ordered_dynamic_failure label_silent s ->
    continuously (now (l_enabled lb_step_ordered_dynamic_failure (tot_map_label l))) (map pt_map_odnet_event s) ->
    continuously (now (l_enabled lb_step_ordered_dynamic_failure l)) s.
Proof.
move => l H_neq s H_exec H_fair.
have H_a: ((lb_step_execution lb_step_ordered_dynamic_failure) /\_ (weak_local_fairness lb_step_ordered_dynamic_failure label_silent)) s by auto.
move: H_a {H_exec H_fair}.
apply: eventually_map_conv_ext => {s}.
- apply extensional_always.
  exact: extensional_now.
- apply extensional_always.
  exact: extensional_now.
- apply extensional_and_tl.
  * exact: lb_step_execution_extensional.
  * exact: weak_local_fairness_extensional.
- rewrite /and_tl /=.
  move => x s [H_e H_w].
  apply lb_step_execution_invar in H_e.
  by apply weak_local_fairness_invar in H_w.
- case => x s [H_a H_w] H_al.
  simpl in *.
  exact: lb_step_ordered_dynamic_failure_weak_fairness_always_enabled_pt_map_onet_continuously.
Qed.

Lemma pt_map_odnet_tot_map_label_event_strong_local_fairness :
  forall s, lb_step_execution lb_step_ordered_dynamic_failure s ->
       strong_local_fairness lb_step_ordered_dynamic_failure label_silent s ->
       strong_local_fairness lb_step_ordered_dynamic_failure label_silent (map pt_map_odnet_event s).
Proof.
move => s.
rewrite /strong_local_fairness => H_exec H_fair l H_neq H_en.
have [l' H_l] := label_tot_mapped l.
rewrite H_l.
apply pt_map_odnet_tot_map_label_event_inf_often_occurred.
apply H_fair; first by move => H_eq; rewrite H_eq pt_lb_label_silent_fst_snd in H_l.
rewrite H_l in H_en.
unfold inf_enabled in *.
apply: pt_map_odnet_tot_map_labeled_event_inf_often_enabled => //.
move => H_eq.
by rewrite -H_l in H_eq.
Qed.

Lemma pt_map_odnet_tot_map_label_event_state_weak_local_fairness : 
  forall s, lb_step_execution lb_step_ordered_dynamic_failure s ->
       weak_local_fairness lb_step_ordered_dynamic_failure label_silent s ->
       weak_local_fairness lb_step_ordered_dynamic_failure label_silent (map pt_map_odnet_event s).
Proof.
move => s.
rewrite /weak_local_fairness => H_exec H_fair l H_neq H_en.
have [l' H_l] := label_tot_mapped l.
rewrite H_l.
apply pt_map_odnet_tot_map_label_event_inf_often_occurred.
apply H_fair; first by move => H_eq; rewrite H_eq pt_lb_label_silent_fst_snd in H_l.
rewrite H_l in H_en.
unfold cont_enabled in *.
apply: pt_map_odnet_tot_map_labeled_event_state_continuously_enabled => //.
move => H_eq.
by rewrite -H_l in H_eq.
Qed.

Context {new_msg_fst : NewMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {new_msg_snd : NewMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {new_msg_map_congr : NewMsgParamsPartialMapCongruency new_msg_fst new_msg_snd msg_map}.

Lemma pt_map_odnet_hd_step_ordered_dynamic_failure_star : 
  forall e, event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init e ->
       event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (pt_map_odnet_event e).
Proof.
move => e.
rewrite /= /pt_map_odnet_event /= /event_step_star /=.
move => H_star.
break_exists.
destruct e, evt_a.
simpl in *.
exact: step_ordered_dynamic_failure_pt_mapped_simulation_star_1.
Qed.

Lemma pt_map_odnet_hd_step_ordered_dynamic_failure_star_always : 
  forall s, event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_dynamic_failure s ->
       always (now (event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init)) (map pt_map_odnet_event s).
Proof.
case => e s H_star H_exec.
apply: step_ordered_dynamic_failure_star_lb_step_execution; first exact: pt_map_odnet_hd_step_ordered_dynamic_failure_star.
exact: lb_step_execution_lb_step_ordered_dynamic_failure_pt_map_odnet_infseq.
Qed.

End PartialMapExecutionSimulations.
