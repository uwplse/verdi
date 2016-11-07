Require Import Verdi.Verdi.

Require Import StructTact.Update.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Relation_Definitions.
Require Import RelationClasses.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Section DynamicNetLemmas.

Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.
Context {overlay_params : NameOverlayParams multi_params}.
Context {new_msg_params : NewMsgParams multi_params}.
Context {fail_msg_params : FailMsgParams multi_params}.

Lemma ordered_dynamic_uninitialized_state :
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, ~ In n (odnwNodes net) ->
 odnwState net n = None.
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes => {H_init}.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update /=.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_not_in: ~ In n (odnwNodes net0) by move => H_not_in; case: H_in; right.
  case name_eq_dec => H_dec; first by rewrite H_dec in H_neq.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update /=.
  have H_neq: n <> to by move => H_eq; rewrite H_eq in H_in.
  case name_eq_dec => H_dec //.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update.
  have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
  case name_eq_dec => H_dec //.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_initialized_state :
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n (odnwNodes net) ->
 exists d, odnwState net n = Some d.
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  case: H_in => H_in.
    rewrite -H_in /update.
    break_if => //.
    by exists (init_handlers h).
  have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
  have [d H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  exists d.
  rewrite /update /=.
  by break_if.
- move => n H_in.
  rewrite /update.
  break_if; first by exists d'.
  have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  by exists d0.
- move => n H_in.
  rewrite /update.
  break_if; first by exists d'.
  have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  by exists d0.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_failed_then_initialized :
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n failed ->
 In n (odnwNodes net).
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {2}H_eq_o {H_eq_o}.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  right.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  case: H_in => H_in; first by rewrite -H_in.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_state_not_initialized_not_failed : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, ~ In n (odnwNodes net) ->
 ~ In n failed.
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {1}H_eq_o {H_eq_o}.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  have H_not_in: ~ In n (odnwNodes net0) by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  move => H_or.
  case: H_or => H_or; first by repeat find_rewrite.
  contradict H_or.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_no_outgoing_uninitialized :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n, ~ In n (odnwNodes onet) ->
  forall n', onet.(odnwPackets) n n' = [].
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes => {H_init}.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_a n'. 
  have H_neq: h <> n by eauto.
  have H_not_in: ~ In n (odnwNodes net0) by eauto.
  rewrite collate_ls_not_in; first by rewrite collate_neq //; eauto.
  apply: not_in_not_in_filter_rel.
  move => H_in.
  case: H_not_in.
  move: H_in.
  exact: in_remove_all_was_in.
- move => n H_a n'.
  have H_neq: to <> n by move => H_eq; rewrite -H_eq in H_a.
  rewrite collate_neq //.
  rewrite /update2.
  case sumbool_and => H_and; last by eauto.
  break_and; repeat find_rewrite.
  simpl in *.
  have IH := IHrefl_trans_1n_trace1 _ H_a.
  by find_higher_order_rewrite.
- move => n H_a n'.
  have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_a.
  rewrite collate_neq //.
  by eauto.
- move => n H_a n'.
  have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_a.
  rewrite collate_neq //.
  by eauto.
Qed.

Lemma ordered_dynamic_nodes_no_dup :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  NoDup (odnwNodes onet).
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /=.
  exact: NoDup_nil.
concludes => {H_init}.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite //=.
exact: NoDup_cons.
Qed.

End DynamicNetLemmas.
