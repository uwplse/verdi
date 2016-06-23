Require Import List.

Require Import Net.
Require Import StructTact.StructTactics.

Class InverseTraceRelation `{State : Type} `{Event : Type} (step : step_relation State Event) :=
  {
    init : State;
    T : (list Event) -> Prop;
    R : State -> Prop;
    R_dec : forall s, {R s} + {~ R s};
    T_monotonic : forall tr o, T tr -> T (tr ++ o);
    R_false_init : ~ R init;
    R_implies_T : forall s s' o tr,
                    refl_trans_1n_trace step init s tr ->
                    ~ R s ->
                    step s s' o ->
                    R s' ->
                    T (tr ++ o)
  }.

Section InverseTraceRelations.
  Context `{ITR : InverseTraceRelation}.
  
  Theorem inverse_trace_relations_work :
    forall s tr,
      refl_trans_1n_trace step init s tr ->
      R s ->
      T tr.
  Proof.
    intros. find_apply_lem_hyp refl_trans_1n_n1_trace.
    remember init as s'.
    induction H.
    - subst. exfalso. eauto using R_false_init.
    - subst. concludes.
      destruct (R_dec x');
        intuition eauto using T_monotonic, refl_trans_n1_1n_trace, R_implies_T.
  Qed.
End InverseTraceRelations.
