Require Import List.
Import ListNotations.
Require Import Net.

Class StateMachineUpgradeParams :=
  {
   input : Type;
   output : Type;

   data1 : Type;
   init : data1;

   input_handlers1 : input -> data1 -> output * data1;

   data2 : Type;
   input_handlers2 : input -> data2 -> output * data2;

   upgrade : data1 -> data2
  }.

Section StepU1.
  Context {p : StateMachineUpgradeParams}.

  Inductive version :=
  | One
  | Two.

  Definition data (v : version) : Type :=
    match v with
    | One => data1
    | Two => data2
    end.

  Definition world := sigT data.

  Definition input_handler (i : input) (w : world) : output * world :=
    let (v, d) := w in
    match v as v' return data v' -> output * world with
    | One => fun d => let (o, d') := input_handlers1 i d in (o, existT _ One d')
    | Two => fun d => let (o, d') := input_handlers2 i d in (o, existT _ Two d')
    end d.

  Inductive step_u1 : (step_relation world (input * output)) :=
  | S1T_deliver : forall (i : input) s s' (out : output),
                    input_handler i s = (out, s') ->
                    step_u1 s s' [(i, out)].

  Definition step_u1_star := refl_trans_1n_trace step_u1.
End StepU1.
