Require Import Verdi.Verdi.
Require Import Verdi.LabeledNet.
Require Import Verdi.TotalMapSimulations.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.map.
Require Import InfSeqExt.exteq.

Require Import FunctionalExtensionality.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import Verdi.Ssrexport.

Set Implicit Arguments.

Class LabeledMultiParamsLabelTotalMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1) :=
  {    
    tot_map_label : @label B0 P0 -> @label B1 P1
  }.

Section LabeledTotalMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.

Definition tot_mapped_lb_net_handlers_label me src m st :=
  let '(lb, out, st', ps) := lb_net_handlers me src m st in tot_map_label lb.

Definition tot_mapped_lb_input_handlers_label me inp st :=
  let '(lb, out, st', ps) := lb_input_handlers me inp st in tot_map_label lb.

End LabeledTotalMapDefs.

Class LabeledMultiParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1)
  (B : BaseParamsTotalMap B0 B1) 
  (N : MultiParamsNameTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (P : MultiParamsMsgTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (L : LabeledMultiParamsLabelTotalMap P0 P1) : Prop :=
  {
    tot_lb_net_handlers_eq : forall me src m st out st' ps lb, 
      lb_net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st) = (lb, out, st', ps)  ->
      tot_mapped_lb_net_handlers_label me src m st = lb ;
    tot_lb_input_handlers_eq : forall me inp st out st' ps lb, 
      lb_input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st) = (lb, out, st', ps) ->
      tot_mapped_lb_input_handlers_label me inp st = lb ;
    tot_lb_label_silent_fst_snd : tot_map_label label_silent = label_silent
  }.

Section TotalMapExecutionSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {msg_map : MultiParamsMsgTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsTotalMapCongruency base_map name_map msg_map}.
Context {multi_map_lb_congr : LabeledMultiParamsTotalMapCongruency base_map name_map msg_map label_map}.

Hypothesis tot_map_label_injective :
  forall l l', tot_map_label l = tot_map_label l' -> l = l'.

(* lb_step_failure *)

Theorem lb_step_failure_tot_mapped_simulation_1 :
  forall net net' failed failed' lb tr,
    @lb_step_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_failure _ labeled_multi_snd (List.map tot_map_name failed, tot_map_net net) (tot_map_label lb) (List.map tot_map_name failed', tot_map_net net') (List.map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
move => net net' failed failed' lb tr H_step.
invcs H_step => //=.
- have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by destruct p.
  apply: (@LabeledStepFailure_deliver _ _ _ _ _ _ (List.map tot_map_packet xs) (List.map tot_map_packet ys) (List.map tot_map_output out) (tot_map_data d) (@tot_map_name_msgs _ _ _ _ _ msg_map l)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * destruct p.
    simpl in *.
    exact: not_in_failed_not_in.
  * destruct p.
    simpl in *.
    rewrite tot_map_name_inv_inverse.
    have H_q := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst).
    rewrite /tot_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_net_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite /tot_map_net /= 2!map_app -(@tot_map_update_packet_eq _ _ _ _ _ _ _ name_map_bijective).
    destruct p.
    by rewrite tot_map_packet_map_eq.
- apply: (@LabeledStepFailure_input _ _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /tot_map_net /= tot_map_name_inv_inverse.
    have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_input_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_input_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * by rewrite /tot_map_net /= map_app tot_map_packet_map_eq -(@tot_map_update_eq _ _ _ _ _ _ name_map_bijective).
- rewrite tot_lb_label_silent_fst_snd.
  exact: LabeledStepFailure_stutter.
Qed.

Definition tot_map_net_event e :=
{| evt_a := (List.map tot_map_name (fst e.(evt_a)), tot_map_net (snd e.(evt_a))) ;
   evt_l := tot_map_label e.(evt_l) ;
   evt_trace := List.map tot_map_trace_occ e.(evt_trace) |}.

Lemma tot_map_net_event_map_unfold : forall s,
 Cons (tot_map_net_event (hd s)) (map tot_map_net_event (tl s)) = map tot_map_net_event s.
Proof using.
by move => s; rewrite -map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_trace_execution_lb_step_failure_tot_map_net_infseq : forall s,
  lb_step_execution lb_step_failure s ->
  lb_step_execution lb_step_failure (map tot_map_net_event s).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
cofix c.
move => s H_exec.
rewrite -tot_map_net_event_map_unfold {1}/tot_map_net_event /=.
inversion H_exec; subst => /=.
rewrite -tot_map_net_event_map_unfold /= /tot_map_net_event /=.
apply: (@Cons_lb_step_exec _ _ _ _ _ _ (List.map tot_map_trace_occ tr)) => /=.
- apply: lb_step_failure_tot_mapped_simulation_1.
  have <-: evt_a e = (fst (evt_a e), snd (evt_a e)) by destruct e, evt_a.
  by have <-: evt_a e' = (fst (evt_a e'), snd (evt_a e')) by destruct e', evt_a.
- simpl in *.
  find_rewrite.
  by rewrite map_app.
- set e0 := {| evt_a := _ ; evt_l := _ ; evt_trace := _ |}.
  have ->: e0 = tot_map_net_event e' by [].
  pose s' := Cons e' s0.
  rewrite (tot_map_net_event_map_unfold s').
  exact: c.
Qed.

Lemma tot_map_net_label_event_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (map tot_map_net_event s).
Proof using.
move => l.
apply: always_map.
apply: eventually_map.
case => e s.
rewrite /= /occurred /=.
move => H_eq.
by rewrite H_eq.
Qed.

Lemma tot_map_net_label_event_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (map tot_map_net_event s) ->
    inf_often (now (occurred l)) s.
Proof using tot_map_label_injective.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- case => e s.
  rewrite /= /occurred /=.
  move => H_eq.
  exact: tot_map_label_injective.
Qed.

Context {fail_fst : FailureParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_snd : FailureParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_map_congr : FailureParamsTotalMapCongruency fail_fst fail_snd base_map}.

Lemma tot_map_net_hd_step_failure_star_always : 
  forall s, event_step_star step_failure step_failure_init (hd s) ->
       lb_step_execution lb_step_failure s ->
       always (now (event_step_star step_failure step_failure_init)) (map tot_map_net_event s).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr fail_map_congr.
case => e s H_star H_exec.
apply: step_failure_star_lb_step_execution.
  rewrite /=.
  rewrite /tot_map_net_event /= /event_step_star /=.
  apply: step_failure_tot_mapped_simulation_star_1.
  by have <-: evt_a e = (fst (evt_a e), snd (evt_a e)) by destruct e, evt_a.
exact: lb_step_trace_execution_lb_step_failure_tot_map_net_infseq.
Qed.

(* lb_step_ordered_failure *)

Theorem lb_step_ordered_failure_tot_mapped_simulation_1 :
  forall net net' failed failed' lb tr,
    @lb_step_ordered_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_ordered_failure _ labeled_multi_snd (List.map tot_map_name failed, tot_map_onet net) (tot_map_label lb) (List.map tot_map_name failed', tot_map_onet net') (List.map tot_map_trace tr).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
move => net net' failed failed' lb tr H_step.
invcs H_step => //=.
- apply (@LabeledStepOrderedFailure_deliver _ _ _ _ _ _ (@tot_map_msg _ _ _ _ msg_map m) (List.map (@tot_map_msg _ _ _ _ msg_map) ms) (List.map tot_map_output out) (tot_map_data d) (@tot_map_name_msgs _ _ _ _ _ msg_map l) (@tot_map_name _ _ _ _ name_map from) (@tot_map_name _ _ _ _ name_map to)) => //=.
  * rewrite /tot_map_onet /=.
    rewrite 2!tot_map_name_inv_inverse.
    by find_rewrite.
  * exact: not_in_failed_not_in.
  * rewrite /tot_map_onet /= tot_map_name_inv_inverse.
    have H_q := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr to from m (onwState net to).
    rewrite /tot_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_net_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite /tot_map_onet /=.         
    rewrite (@collate_tot_map_update2_eq _ _ _ _ _ _ name_map_bijective).
    set f1 := fun _ => tot_map_data _.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2.
      apply functional_extensionality => n.
      rewrite /update.
      break_if; break_if => //; first by rewrite -e tot_map_name_inverse_inv in n0.
      by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite (@map_tot_map_trace_eq _ _ _ _ _ name_map).
- rewrite /tot_map_onet /=.
  apply (@LabeledStepOrderedFailure_input _ _ (@tot_map_name _ _ _ _ name_map h) _ _ _ _ (List.map tot_map_output out) (tot_map_input inp) (tot_map_data d) (@tot_map_name_msgs _ _ _ _ _ msg_map l)).
  * exact: not_in_failed_not_in.
  * rewrite /tot_map_onet /= tot_map_name_inv_inverse.
    have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h inp (onwState net h).
    rewrite /tot_mapped_input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_input_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_input_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite /tot_map_onet /=.
    rewrite (@collate_tot_map_eq _ _ _ _ _ _ name_map_bijective).
    set f1 := fun _ => tot_map_data _.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2.
      apply functional_extensionality => n.
      rewrite /update.
      break_if; break_if => //; first by rewrite -e tot_map_name_inverse_inv in n0.
      by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite (@map_tot_map_trace_eq _ _ _ _ _ name_map).
- rewrite tot_lb_label_silent_fst_snd.
  exact: LabeledStepOrderedFailure_stutter.
Qed.

Definition tot_map_onet_event e :=
{| evt_a := (List.map tot_map_name (fst e.(evt_a)), tot_map_onet (snd e.(evt_a))) ;
   evt_l := tot_map_label e.(evt_l) ;
   evt_trace := List.map tot_map_trace e.(evt_trace) |}.

Lemma tot_map_onet_event_map_unfold : forall s,
 Cons (tot_map_onet_event (hd s)) (map tot_map_onet_event (tl s)) = map tot_map_onet_event s.
Proof using.
by move => s; rewrite -map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_execution_lb_step_ordered_failure_tot_map_onet_infseq : forall s,
  lb_step_execution lb_step_ordered_failure s ->
  lb_step_execution lb_step_ordered_failure (map tot_map_onet_event s).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
cofix c.
move => s H_exec.
rewrite -tot_map_onet_event_map_unfold {1}/tot_map_onet_event /=.
inversion H_exec; subst => /=.
rewrite -tot_map_onet_event_map_unfold /= /tot_map_onet_event /=.
apply: (@Cons_lb_step_exec _ _ _ _ _ _ (List.map tot_map_trace tr)) => /=.
- apply: lb_step_ordered_failure_tot_mapped_simulation_1.
  have <-: evt_a e = (fst (evt_a e), snd (evt_a e)) by destruct e, evt_a.
  by have <-: evt_a e' = (fst (evt_a e'), snd (evt_a e')) by destruct e', evt_a.
- simpl in *.
  find_rewrite.
  by rewrite map_app.
- set e0 := {| evt_a := _ ; evt_l := _ ; evt_trace := _ |}.
  have ->: e0 = tot_map_onet_event e' by [].
  pose s' := Cons e' s0.
  rewrite (tot_map_onet_event_map_unfold s').
  exact: c.
Qed.

Lemma tot_map_onet_label_event_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (map tot_map_onet_event s).
Proof using.
move => l.
apply: always_map.
apply: eventually_map.
case => e s.
rewrite /= /occurred /=.
move => H_eq.
by rewrite H_eq.
Qed.

Lemma tot_map_onet_label_event_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (map tot_map_onet_event s) ->
    inf_often (now (occurred l)) s.
Proof using tot_map_label_injective.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- case => e s.
  rewrite /= /occurred /=.
  move => H_eq.
  exact: tot_map_label_injective.
Qed.  

Context {overlay_fst : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {overlay_snd : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Context {fail_msg_fst : FailMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_msg_snd : FailMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_msg_map_congr : FailMsgParamsTotalMapCongruency fail_msg_fst fail_msg_snd msg_map}.
  
Lemma tot_map_onet_hd_step_ordered_failure_star_always : 
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       always (now (event_step_star step_ordered_failure step_ordered_failure_init)) (map tot_map_onet_event s).
Proof using overlay_map_congr name_map_bijective multi_map_lb_congr multi_map_congr fail_msg_map_congr.
case => e s H_star H_exec.
apply: step_ordered_failure_star_lb_step_execution; last exact: lb_step_execution_lb_step_ordered_failure_tot_map_onet_infseq.
rewrite /= /tot_map_onet_event /= /event_step_star /=.
apply: step_ordered_failure_tot_mapped_simulation_star_1.
by have <-: evt_a e = (fst (evt_a e), snd (evt_a e)) by destruct e, evt_a.
Qed.

(* lb_step_ordered_dynamic_failure *)

Theorem lb_step_ordered_dynamic_failure_tot_mapped_simulation_1 :
  forall net net' failed failed' lb tr,
    @lb_step_ordered_dynamic_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_ordered_dynamic_failure _ labeled_multi_snd (List.map tot_map_name failed, tot_map_odnet net) (tot_map_label lb) (List.map tot_map_name failed', tot_map_odnet net') (List.map tot_map_trace tr).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
move => net net' failed failed' lb tr H_step.
invcs H_step => //=.
- rewrite /tot_map_odnet /=.
  apply (@LabeledStepOrderedDynamicFailure_deliver _ _ _ _ _ _ (@tot_map_msg _ _ _ _ msg_map m) (List.map (@tot_map_msg _ _ _ _ msg_map) ms) (List.map tot_map_output out) (tot_map_data d) (tot_map_data d') (@tot_map_name_msgs _ _ _ _ _ msg_map l) (@tot_map_name _ _ _ _ name_map from) (@tot_map_name _ _ _ _ name_map to)) => //=.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in. 
  * rewrite tot_map_name_inv_inverse.
    by find_rewrite.
  * rewrite 2!tot_map_name_inv_inverse.
    by find_rewrite.
  * have H_q := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr to from m d.
    rewrite /tot_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_net_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite (@collate_tot_map_update2_eq _ _ _ _ _ _ name_map_bijective).
    set f1 := fun _ => match _ with _ => _ end.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2 /update.
      apply functional_extensionality => dst.
      repeat break_if => //=; first by rewrite -e tot_map_name_inverse_inv in n.
      by rewrite e tot_map_name_inv_inverse in n.
    by rewrite H_eq_f.
  * by rewrite (@map_tot_map_trace_eq _ _ _ _ _ name_map).
- rewrite /tot_map_odnet /=.
  apply (@LabeledStepOrderedDynamicFailure_input _ _ (@tot_map_name _ _ _ _ name_map h) _ _ _ _ (List.map tot_map_output out) (tot_map_input inp) (tot_map_data d) (tot_map_data d') (@tot_map_name_msgs _ _ _ _ _ msg_map l)) => //=.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in. 
  * rewrite tot_map_name_inv_inverse.
    by find_rewrite.
  * have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h inp d.
    rewrite /tot_mapped_input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_input_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_input_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite (@collate_tot_map_eq _ _ _ _ _ _ name_map_bijective).
    set f1 := fun _ => match _ with _ => _ end.
    set f2 := update _ _ _ _.
    have H_eq_f: f1 = f2.
      rewrite /f1 /f2 /update.
      apply functional_extensionality => n.
      repeat break_match; try by congruence.
      * by rewrite e tot_map_name_inv_inverse in n0.
      * by rewrite -e tot_map_name_inverse_inv in n0.
      * by rewrite e tot_map_name_inv_inverse in n0.
    by rewrite H_eq_f.
  * by rewrite (@map_tot_map_trace_eq _ _ _ _ _ name_map).
- rewrite tot_lb_label_silent_fst_snd.
  exact: LabeledStepOrderedDynamicFailure_stutter.
Qed.

Definition tot_map_odnet_event e :=
{| evt_a := (List.map tot_map_name (fst e.(evt_a)), tot_map_odnet (snd e.(evt_a))) ;
   evt_l := tot_map_label e.(evt_l) ;
   evt_trace := List.map tot_map_trace e.(evt_trace) |}.

Lemma tot_map_odnet_event_map_unfold : forall s,
 Cons (tot_map_odnet_event (hd s)) (map tot_map_odnet_event (tl s)) = map tot_map_odnet_event s.
Proof using.
by move => s; rewrite -map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_execution_lb_step_ordered_dynamic_failure_tot_map_odnet_infseq : forall s,
  lb_step_execution lb_step_ordered_dynamic_failure s ->
  lb_step_execution lb_step_ordered_dynamic_failure (map tot_map_odnet_event s).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
cofix c.
move => s H_exec.
rewrite -tot_map_odnet_event_map_unfold {1}/tot_map_odnet_event /=.
inversion H_exec; subst => /=.
rewrite -tot_map_odnet_event_map_unfold /= /tot_map_odnet_event /=.
apply: (@Cons_lb_step_exec _ _ _ _ _ _ (List.map tot_map_trace tr)) => /=.
- apply: lb_step_ordered_dynamic_failure_tot_mapped_simulation_1.
  have <-: evt_a e = (fst (evt_a e), snd (evt_a e)) by destruct e, evt_a.
  by have <-: evt_a e' = (fst (evt_a e'), snd (evt_a e')) by destruct e', evt_a.
- simpl in *.
  find_rewrite.
  by rewrite map_app.
- set e0 := {| evt_a := _ ; evt_l := _ ; evt_trace := _ |}.
  have ->: e0 = tot_map_odnet_event e' by [].
  pose s' := Cons e' s0.
  rewrite (tot_map_odnet_event_map_unfold s').
  exact: c.
Qed.

Lemma tot_map_odnet_label_event_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (map tot_map_odnet_event s).
Proof using.
move => l.
apply: always_map.
apply: eventually_map.
case => e s.
rewrite /= /occurred /=.
move => H_eq.
by rewrite H_eq.
Qed.

Lemma tot_map_odnet_label_event_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (map tot_map_odnet_event s) ->
    inf_often (now (occurred l)) s.
Proof using tot_map_label_injective.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- case => e s.
  rewrite /= /occurred /=.
  move => H_eq.
  exact: tot_map_label_injective.
Qed.

Context {new_msg_fst : NewMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {new_msg_snd : NewMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {new_msg_map_congr : NewMsgParamsTotalMapCongruency new_msg_fst new_msg_snd msg_map}.

Lemma tot_map_odnet_hd_step_ordered_dynamic_failure_star_always : 
  forall s, event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_dynamic_failure s ->
       always (now (event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init)) (map tot_map_odnet_event s).
Proof using overlay_map_congr new_msg_map_congr name_map_bijective multi_map_lb_congr multi_map_congr fail_msg_map_congr.
case => e s H_star H_exec.
apply: step_ordered_dynamic_failure_star_lb_step_execution; last exact: lb_step_execution_lb_step_ordered_dynamic_failure_tot_map_odnet_infseq.
rewrite /= /tot_map_odnet_event /= /event_step_star /=.
apply: step_ordered_dynamic_failure_tot_mapped_simulation_star_1.
by have <-: evt_a e = (fst (evt_a e), snd (evt_a e)) by destruct e, evt_a.
Qed.

End TotalMapExecutionSimulations.
