Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Net.

Section ST.
  Context {B : BaseParams}.
  Context {M : MultiParams B}.
  Context {F : FailureParams M}.

  Variable R : network -> list (name * (input + list output)) -> Prop.
  Variable T : list (name * (input + list output)) -> Prop.

  Hypothesis T_snoc_inv : forall ev tr, T (tr ++ [ev]) -> T tr.
  Hypothesis RT_init : T [] -> R step_m_init [].

  Definition RT_deliver : Prop :=
    forall net failed tr xs p ys out d l,
      step_f_star step_f_init (failed, net) tr ->
      T tr ->
      R net tr ->
      nwPackets net = xs ++ p :: ys ->
      net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
      R (mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                   (update (nwState net) (pDst p) d))
        (tr ++ [(pDst p, inr out)]).

  Hypothesis H_RT_deliver : RT_deliver.

  Definition RT_input : Prop :=
    forall net failed tr h i out d l,
      step_f_star step_f_init (failed, net) tr ->
      T tr ->
      R net tr ->
      input_handlers h i (nwState net h) = (out, d, l) ->
      R (mkNetwork (send_packets h l ++ nwPackets net)
                   (update (nwState net) h d))
        (tr ++ [(h, inl i); (h, inr out)]).

  Hypothesis H_RT_input : RT_input.

  Lemma state_trace_invariant_invariant :
    forall failed net tr,
      step_f_star step_f_init (failed, net) tr ->
      T tr ->
      R net tr.
  Proof.
    intros.
    remember (failed, net) as p. generalize dependent failed. revert net.
    remember step_f_init as init. revert Heqinit. revert H0.
    apply refl_trans_1n_n1_trace in H.
    induction H; intros; subst.
    - unfold step_f_init in *. find_inversion. auto.
    - match goal with
        | [ H : step_f _ _ _ |- _ ] => invc H
      end.
      + eapply H_RT_deliver with (failed := failed); eauto.
        apply refl_trans_n1_1n_trace; auto.
      + eapply H_RT_input; eauto. SearchAbout (_ ++ _ :: _).
