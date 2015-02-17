Require Import List.
Import ListNotations.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Class TraceRelation `{State : Type} `{Event : Type} (step : step_relation State Event) :=
  {
    T : (list Event) -> Prop;
    T_dec : forall l, {T l} + {~ T l};
    R : State -> Prop;
    R_monotonic : forall s s' o, step s s' o -> R s -> R s';
    T_false_init : ~ T [];
    T_implies_R : forall tr s s' o,
                    ~ T tr ->
                    step s s' o ->
                    T (tr ++ o) ->
                    R s'
  }.

Section TraceRelations.
  Context `{TR : TraceRelation}.
  
  Theorem trace_relations_work :
    forall s s' tr,
      refl_trans_1n_trace step s s' tr ->
      T tr -> R s'.
  Proof.
    intros. find_apply_lem_hyp refl_trans_1n_n1_trace.
    induction H.
    - intros; exfalso; eauto using T_false_init.
    - destruct (T_dec cs); eauto using R_monotonic, T_implies_R.
  Qed.
End TraceRelations.
