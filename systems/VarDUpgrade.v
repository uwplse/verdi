Require Import Verdi.
Require Import StateMachineUpgrade.
Require Import VarD.

Require Import StringMap.

Module list_to_tree(E : EQUALITY_TYPE) (T : TREE with Definition elt := E.t).
  Module M := ETree(E).

  Fixpoint list_to_tree {V} (l : M.t V) : T.t V :=
    match l with
    | [] => T.empty V
    | (k,v) :: l' => T.set k v (list_to_tree l')
    end.
End list_to_tree.

Module LT := list_to_tree EqString LogTimeStringMap.

Definition upgrade (d : LinearTimeVarD.data) : LogTimeVarD.data :=
  LT.list_to_tree d.

Definition simulation (d1 : LinearTimeVarD.data) (d2 : LogTimeVarD.data) : Prop :=
  forall k, LinearTimeStringMap.get k d1 = LogTimeStringMap.get k d2.

Lemma upgrade_establishes_simulation :
  forall d1,
    simulation d1 (upgrade d1).
Admitted.

Theorem handlers_preserve_simulation :
  forall d1 d2 d1' i o,
    simulation d1 d2 ->
    LinearTimeVarD.VarDHandler i d1 = (o, d1') ->
    exists d2',
      simulation d1' d2' /\
      LogTimeVarD.VarDHandler i d2 = (o, d2').
Admitted.

Instance vard_upgrade_params : StateMachineUpgradeParams :=
 {
   input := VarD.input;
   output := VarD.output;

   data1 := LinearTimeVarD.data;
   init := LinearTimeVarD.init;
   input_handlers1 := LinearTimeVarD.VarDHandler;

   data2 := LogTimeVarD.data;
   input_handlers2 := LogTimeVarD.VarDHandler;

   upgrade := upgrade
 }.