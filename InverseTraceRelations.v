Require Import List.
Import ListNotations.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Class InverseTraceRelation `{State : Type} `{Trace : Type} (step : step_relation State Trace) :=
  {
    T : (list Trace) -> Prop;
    R : State -> Prop;
    R_dec : forall s, {R s} + {~ R s};
    T_monotonic : forall tr o, T tr -> T (tr ++ o);
    R_monotonic : forall s s' o, step s s' o -> R s -> R s';
    R_implies_T : forall s s' o tr,
                    ~ R s ->
                    step s s' o ->
                    R s' ->
                    T (tr ++ o)
  }.

Section InverseTraceRelations.
  Context `{ITR : InverseTraceRelation}.
  
  Theorem inverse_trace_relations_work' :
    forall s s' tr,
      refl_trans_1n_trace step s s' tr ->
      ~ R s ->
      R s' ->
      T tr.
  Proof.
    intros. find_apply_lem_hyp refl_trans_1n_n1_trace.
    induction H.
    - intuition.
    - concludes.
      destruct (R_dec x'); eauto using T_monotonic, R_implies_T.
  Qed.
End InverseTraceRelations.
