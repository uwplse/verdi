Require Import Verdi.Verdi.
Require Import Verdi.DynamicNetLemmas.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class MultiSingleParamsTotalMap
  (B0 : BaseParams) (P0 : MultiParams B0) (B1 : BaseParams) :=
  {
    tot_s_map_data : @data B0 -> @data B1 ;
    tot_s_map_input : name -> @input B0 -> @input B1 ;
    tot_s_map_output : @output B0 -> @output B1 ;
    tot_s_map_msg : name -> name -> msg -> @input B1
  }.

Class MultiSingleParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : SingleParams B1)
  (M : MultiSingleParamsTotalMap P0 B1) (me : name) :=
  {
    tot_s_init_handlers_eq : tot_s_map_data (init_handlers me) = init_handler ;
    tot_s_input_handlers_eq : forall inp st out st' ps out' st'',
      input_handlers me inp st = (out, st', ps) ->
      input_handler (tot_s_map_input me inp) (tot_s_map_data st) = (out', st'') ->
      map tot_s_map_output out = out' /\ tot_s_map_data st' = st''
  }.

Section SingleSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi : MultiParams base_fst}.
Context {overlay : NameOverlayParams multi}.
Context {fail_msg : FailMsgParams multi}.
Context {single : SingleParams base_snd}.
Context {tot_map : MultiSingleParamsTotalMap multi base_snd}.
Context {me : name} {map_congr : MultiSingleParamsTotalMapCongruency single tot_map me}.

Definition step_ordered_failure_tot_s_net_handlers_eq :=
  forall net failed tr src m ms out st' ps out' st'',
  step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
  onwPackets net src me = m :: ms ->
  ~ In me failed ->
  net_handlers me src m (onwState net me) = (out, st', ps) ->
  input_handler (tot_s_map_msg me src m) (tot_s_map_data (onwState net me)) = (out', st'') ->
  map tot_s_map_output out = out' /\ tot_s_map_data st' = st''.

Theorem step_ordered_failure_tot_one_mapped_simulation_1 :
  step_ordered_failure_tot_s_net_handlers_eq ->
  forall net net' failed failed' tr tr',    
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
    step_ordered_failure (failed, net) (failed', net') tr' ->
    net.(onwState) me = net'.(onwState) me \/
    exists tr'', @step_s _ single (tot_s_map_data (net.(onwState) me)) (tot_s_map_data (net'.(onwState) me)) tr''.
Proof.
move => H_net_eq net net' failed failed' tr tr' H_star H_step.
invcs H_step.
- rewrite /update.
  break_if; last by left.
  right.
  subst_max.
  case H_hnd: (input_handler (tot_s_map_msg me from m) (tot_s_map_data (onwState net me))) => [out' d'].
  have H_eq := H_net_eq _ _ _ _ _ _ _ _ _ _ _ H_star H3 H4 H5 H_hnd.
  break_and.
  exists (inl (tot_s_map_msg me from m) :: (map inr out')).
  apply: SST_deliver => //=.
  by rewrite H_hnd H0.
- rewrite /update.
  break_if; last by left.
  right.
  subst_max.
  case H_hnd: (input_handler (tot_s_map_input me inp) (tot_s_map_data (onwState net me))) => [out' d'].
  have H_eq_inp := @tot_s_input_handlers_eq _ _ _ _ _ _ map_congr _ _ _ _ _ _ _ H4 H_hnd.
  break_and.
  exists (inl (tot_s_map_input me inp) :: map inr out').
  apply: SST_deliver => //=.
  by rewrite H_hnd H0.
- by left.
Qed.

Lemma step_ordered_failure_tot_one_mapped_simulation_star_1 :
  step_ordered_failure_tot_s_net_handlers_eq ->
  forall net failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
    exists tr', @step_s_star _ single init_handler (tot_s_map_data (net.(onwState) me)) tr'.
Proof.
move => H_net_eq net failed tr H_st.
have ->: net = snd (failed, net) by [].
remember step_ordered_failure_init as y in H_st.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /=.
  exists [].
  rewrite tot_s_init_handlers_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_st1 H_st2.
case: x' H IHH_st1 H_st1 => failed' net'.
case: x'' H_st2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
have [tr' H_star] := IHH_step1.
have H_st := step_ordered_failure_tot_one_mapped_simulation_1 H_net_eq H_step1 H.
case: H_st => H_st; first by rewrite -H_st; exists tr'.
have [tr'' H_st'] := H_st.
exists (tr' ++ tr'').
apply: (refl_trans_1n_trace_trans H_star).
have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
apply RT1nTStep with (x' := (tot_s_map_data (onwState net'' me))) => //.
exact: RT1nTBase.
Qed.

Context {new_msg : NewMsgParams multi}.

Definition step_ordered_dynamic_failure_tot_s_net_handlers_eq :=
  forall net failed tr src m ms d out st' ps out' st'',
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
  odnwPackets net src me = m :: ms ->
  ~ In me failed ->
  odnwState net me = Some d ->
  net_handlers me src m d = (out, st', ps) ->
  input_handler (tot_s_map_msg me src m) (tot_s_map_data d) = (out', st'') ->
  map tot_s_map_output out = out' /\ tot_s_map_data st' = st''.

Theorem step_ordered_dynamic_failure_tot_one_mapped_simulation_1 :
  step_ordered_dynamic_failure_tot_s_net_handlers_eq ->
  forall net net' failed failed' tr tr',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    step_ordered_dynamic_failure (failed, net) (failed', net') tr' ->
    forall d, net.(odnwState) me = Some d ->
    forall d', net'.(odnwState) me = Some d' ->
    d = d' \/ exists tr'', @step_s _ single (tot_s_map_data d) (tot_s_map_data d') tr''.
Proof.
move => H_net_eq net net' failed failed' tr tr' H_star H_step d H_eq d' H_eq'.
invcs H_step.
- left.
  have H_neq: h <> me.
    move => H_n.
    rewrite -H_n in H_eq.
    have H_eq_n := ordered_dynamic_uninitialized_state H_star _ H4.
    by congruence.
  move: H_eq'.
  rewrite /update.
  break_if; first by find_rewrite.
  by congruence.
- move: H_eq'.
  rewrite /update.
  break_if => H_eq'; last by left; congruence.    
  right.
  find_injection.
  rewrite H_eq in H5.
  find_injection.
  case H_hnd: (input_handler (tot_s_map_msg me from m) (tot_s_map_data d0)) => [out' d''].
  have H_eq_st := H_net_eq _ _ _ _ _ _ _ _ _ _ _ _ H_star H6 H3 H_eq H7 H_hnd.
  break_and.
  exists (inl (tot_s_map_msg me from m) :: (map inr out')).
  apply: SST_deliver => //=.
  by rewrite H_hnd H0.
- move: H_eq'.
  rewrite /update.
  break_if => H_eq'; last by left; rewrite H_eq in H_eq'; find_injection.
  right.
  find_injection.
  rewrite H_eq in H5.
  find_injection.
  case H_hnd: (input_handler (tot_s_map_input me inp) (tot_s_map_data d0)) => [out' d''].
  have H_eq_inp := @tot_s_input_handlers_eq _ _ _ _ _ _ map_congr _ _ _ _ _ _ _ H6 H_hnd.
  break_and.
  exists (inl (tot_s_map_input me inp) :: map inr out').
  apply: SST_deliver => //=.
  by rewrite H_hnd H0.
- left.
  find_rewrite.
  by find_injection.
Qed.

Lemma step_ordered_dynamic_failure_tot_one_mapped_simulation_1_init :
  forall net net' failed failed' tr,
    step_ordered_dynamic_failure (failed, net) (failed', net') tr ->
    net.(odnwState) me = None ->
    forall d, net'.(odnwState) me = Some d ->
    tot_s_map_data d = init_handler.
Proof.
move => net net' failed failed' tr H_st H_eq d H_eq'.
invcs H_st => //=.
- move: H_eq'.
  rewrite /update.
  break_if => H_eq'; last by congruence.
  find_injection.
  by rewrite tot_s_init_handlers_eq.
- move: H_eq'.
  rewrite /update.
  by break_if => H_eq'; congruence.
- move: H_eq'.
  rewrite /update.
  by break_if => H_eq'; congruence.
- by congruence.
Qed.

Lemma step_ordered_dynamic_failure_tot_one_mapped_simulation_star_1 :
  step_ordered_dynamic_failure_tot_s_net_handlers_eq ->
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall d, net.(odnwState) me = Some d ->
    exists tr', @step_s_star _ single init_handler (tot_s_map_data d) tr'.
Proof.
move => H_net_eq net failed tr H_st.
have ->: net = snd (failed, net) by [].
remember step_ordered_dynamic_failure_init as y in H_st.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init.
concludes.
rewrite H_init {H_init x} in H_st1 H_st2.
case: x' H IHH_st1 H_st1 => failed' net'.
case: x'' H_st2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1 d H_eq.
case H_eq': (odnwState net' me) => [d'|]; last first.
  exists [].
  have H_eq_i := step_ordered_dynamic_failure_tot_one_mapped_simulation_1_init H H_eq' H_eq.
  rewrite H_eq_i.
  exact: RT1nTBase.
have [tr' H_star] := IHH_step1 _ H_eq'.
have H_st := step_ordered_dynamic_failure_tot_one_mapped_simulation_1 H_net_eq H_step1 H H_eq' H_eq.
case: H_st => H_st; first by rewrite -H_st; exists tr'.
have [tr'' H_st'] := H_st.
exists (tr' ++ tr'').
apply: (refl_trans_1n_trace_trans H_star).
have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
apply RT1nTStep with (x' := (tot_s_map_data d)) => //.
exact: RT1nTBase.
Qed.

End SingleSimulations.
