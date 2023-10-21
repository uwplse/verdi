From Verdi Require Import Verdi.
From Coq Require Import String.
From Verdi Require Import VarD PrimaryBackup.

Open Scope string_scope.

#[global]
Instance vard_pbj_params : PrimaryBackupParams vard_base_params :=
  {
    input_eq_dec := VarD.input_eq_dec
  }.

Theorem lifting_applied :
  forall (net : @network _ PB_multi_params) tr,
    step_async_star step_async_init net tr ->
    trace_correct (revert_trace (base_params := vard_base_params) tr).
Proof.
  apply transformer.
  eauto using step_1_star_trace_correct.
Qed.

Example revert_trace_primary_empty :
  revert_trace [(Primary, inl (Request (Put "james" "awesome")))] = [].
Proof.
  reflexivity.
Qed.

Example revert_trace_eg :
  forall net tr o,
    step_async_star (params := PB_multi_params) step_async_init net tr ->
    inputs_m tr = [Put "james" "awesome"] ->
    outputs_m tr = [o] ->
    o = Response "james" (Some "awesome") None.
Proof.
  intros.
  find_copy_apply_lem_hyp simulation.
  find_copy_apply_lem_hyp pbj_NOABT.
  find_apply_lem_hyp outputs_m_revert_trace.
  find_copy_apply_lem_hyp inputs_1_m_revert.
  find_copy_apply_lem_hyp lifting_applied.

  repeat find_rewrite.
  destruct (revert_trace tr); try discriminate.
  simpl in *. find_inversion. destruct l; try discriminate.
  simpl in *.
  find_inversion.
  repeat find_reverse_rewrite.

  find_copy_eapply_lem_hyp correspond_reachable; eauto.
  - invc H5. destruct t.
    + simpl in *. repeat find_inversion. simpl in *. subst. simpl in *. find_inversion. auto.
    + destruct t; discriminate.
  - simpl. congruence.
Qed.

Example get_set_eg1 :
  forall tr (net : @network _ PB_multi_params) a b,
    step_async_star step_async_init net tr ->
    inputs_m tr = [Put "james" "awesome"; Get "james"] ->
    outputs_m tr = [a; b] ->
    outputs_m tr = [Response "james" (Some "awesome") None;
                     Response "james" (Some "awesome") (Some "awesome")].
Proof.
  intros.
  find_copy_apply_lem_hyp simulation.
  find_copy_apply_lem_hyp pbj_NOABT.
  find_apply_lem_hyp outputs_m_revert_trace.
  find_copy_apply_lem_hyp inputs_1_m_revert.
  find_copy_apply_lem_hyp lifting_applied.

  repeat find_rewrite.
  destruct (revert_trace tr); try discriminate.
  simpl in *. find_inversion. destruct l; try discriminate.
  simpl in *.
  find_inversion.
  destruct l; try discriminate.
  simpl in *.
  find_inversion.
  repeat find_reverse_rewrite.

  find_copy_eapply_lem_hyp correspond_reachable; eauto.
  - invc H5.
    destruct t; simpl in *; repeat find_inversion.
    destruct t; simpl in *; repeat find_inversion.
    + simpl in *. invc H8. destruct t; simpl in *.
      * repeat find_inversion. simpl in *. repeat find_rewrite.
        subst. simpl in *. find_inversion. auto.
      * repeat find_inversion. destruct t; discriminate.
    + destruct t; discriminate.
  - simpl. congruence.
Qed.
