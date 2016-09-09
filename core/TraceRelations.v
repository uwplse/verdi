Require Import List.
Import ListNotations.

Require Import Verdi.Net.
Require Import StructTact.StructTactics.

Class TraceRelation `{State : Type} `{Event : Type} (step : step_relation State Event) :=
  {
    init : State;
    T : (list Event) -> Prop;
    T_dec : forall l, {T l} + {~ T l};
    R : State -> Prop;
    R_monotonic : forall s s' tr o, refl_trans_1n_trace step init s tr ->
                               step s s' o ->
                               R s ->
                               R s';
    T_false_init : ~ T [];
    T_implies_R : forall tr s s' o,
                    refl_trans_1n_trace step init s tr ->
                    ~ T tr ->
                    step s s' o ->
                    T (tr ++ o) ->
                    R s'
  }.

Section TraceRelations.
  Context `{TR : TraceRelation}.
  
  Theorem trace_relations_work :
    forall s tr,
      refl_trans_1n_trace step init s tr ->
      T tr -> R s.
  Proof.
    intros.
    find_copy_apply_lem_hyp refl_trans_1n_n1_trace.
    remember init as s'.
    induction H1.
    - intros; exfalso; eauto using T_false_init.
    - subst. destruct (T_dec cs); intuition eauto using R_monotonic, refl_trans_n1_1n_trace, T_implies_R.
  Qed.
End TraceRelations.
