Require Import FunctionalExtensionality.

Require Import Verdi.

Section ST.
  Context {B : BaseParams}.
  Context {M : MultiParams B}.
  Context {F : FailureParams M}.

  Variable R : network -> list (name * (input + list output)) -> Prop.
  Variable T : list (name * (input + list output)) -> Prop.

  Hypothesis T_snoc_inv : forall ev tr, T (tr ++ [ev]) -> T tr.
  Hypothesis RT_init : T [] -> R step_async_init [].

  Definition RT_deliver : Prop :=
    forall net failed tr xs p ys out d l,
      step_failure_star step_failure_init (failed, net) tr ->
      T tr ->
      R net tr ->
      nwPackets net = xs ++ p :: ys ->
      net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
      R (mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                   (update name_eq_dec (nwState net) (pDst p) d))
        (tr ++ [(pDst p, inr out)]).

  Hypothesis H_RT_deliver : RT_deliver.

  Definition RT_input : Prop :=
    forall net failed tr h i out d l,
      step_failure_star step_failure_init (failed, net) tr ->
      T (tr ++ [(h, inl i)]) ->
      R net tr ->
      input_handlers h i (nwState net h) = (out, d, l) ->
      R (mkNetwork (send_packets h l ++ nwPackets net)
                   (update name_eq_dec (nwState net) h d))
        (tr ++ [(h, inl i); (h, inr out)]).

  Hypothesis H_RT_input : RT_input.

  Definition RT_drop : Prop :=
    forall net failed tr xs p ys,
      step_failure_star step_failure_init (failed, net) tr ->
      T tr ->
      R net tr ->
      nwPackets net = xs ++ p :: ys ->
      R (mkNetwork (xs ++ ys) (nwState net))
        tr.

  Hypothesis H_RT_drop : RT_drop.

  Definition RT_dup : Prop :=
    forall net failed tr xs p ys,
      step_failure_star step_failure_init (failed, net) tr ->
      T tr ->
      R net tr ->
      nwPackets net = xs ++ p :: ys ->
      R (mkNetwork (p :: xs ++ p :: ys) (nwState net))
        tr.

  Hypothesis H_RT_dup : RT_dup.

  Definition RT_reboot : Prop :=
    forall net failed tr h,
      step_failure_star step_failure_init (failed, net) tr ->
      T tr ->
      R net tr ->
      R (mkNetwork (nwPackets net) (update name_eq_dec (nwState net) h (reboot (nwState net h))))
        tr.

  Hypothesis H_RT_reboot : RT_reboot.

  Lemma state_trace_invariant_invariant :
    forall failed net tr,
      step_failure_star step_failure_init (failed, net) tr ->
      T tr ->
      R net tr.
  Proof.
    intros.
    remember (failed, net) as p. generalize dependent failed. revert net.
    remember step_failure_init as init. revert Heqinit. revert H0.
    apply refl_trans_1n_n1_trace in H.
    induction H; intros; subst.
    - unfold step_failure_init in *. find_inversion. auto.
    - match goal with
        | [ H : step_failure _ _ _ |- _ ] => invc H
      end.
      + eapply H_RT_deliver with (failed := failed); eauto.
        apply refl_trans_n1_1n_trace; auto.
      + eapply H_RT_input with (failed:=failed); eauto.
        * apply refl_trans_n1_1n_trace; auto.
        * eapply T_snoc_inv. rewrite app_ass. simpl. eauto.
        * eapply IHrefl_trans_n1_trace; eauto.
          eapply T_snoc_inv. eapply T_snoc_inv.
          rewrite app_ass. simpl. eauto.
      + rewrite app_nil_r in *.
        eapply H_RT_drop with (failed:=failed); eauto.
        apply refl_trans_n1_1n_trace. eauto.
      + rewrite app_nil_r in *.
        eapply H_RT_dup; eauto.
        apply refl_trans_n1_1n_trace. eauto.
      + rewrite app_nil_r in *. eauto.
      + rewrite app_nil_r in *.
        repeat concludes.
        find_insterU. find_insterU.  conclude_using eauto.
        eapply H_RT_reboot in IHrefl_trans_n1_trace; eauto.
        * unfold update in *.
          replace (fun nm : name =>
                if name_eq_dec nm h
                then reboot (nwState net0 nm)
                else nwState net0 nm)
                  with (fun nm : name =>
                if name_eq_dec nm h
                then reboot (nwState net0 h)
                else nwState net0 nm );
          eauto.
          apply functional_extensionality.
          intros. break_if; congruence.
        * apply refl_trans_n1_1n_trace. eauto.
  Qed.
End ST.
