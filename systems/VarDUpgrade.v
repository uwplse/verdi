Require Import Verdi.
Require Import StateMachineUpgrade.
Require Import VarD.

Require Import StringMap.

Module list_to_tree(E : EQUALITY_TYPE) (T : TREE
                                           with Definition elt := E.t
                                           with Definition elt_eq := E.eq).
  Module M := ETree(E).

  Fixpoint list_to_tree {V} (l : M.t V) : T.t V :=
    match l with
    | [] => T.empty V
    | (k,v) :: l' => T.set k v (list_to_tree l')
    end.

  Lemma list_to_tree_equiv :
    forall V (l : M.t V) k,
      M.get k l = T.get k (list_to_tree l).
  Proof.
    induction l; simpl; intros.
    - now rewrite T.gempty.
    - destruct a.
      rewrite T.gsspec.
      unfold T.elt_eq.
      break_if; auto.
  Qed.
End list_to_tree.

Module LT := list_to_tree EqString LogTimeStringMap.

Definition upgrade (d : LinearTimeVarD.data) : LogTimeVarD.data :=
  LT.list_to_tree d.

Definition simulation (d1 : LinearTimeVarD.data) (d2 : LogTimeVarD.data) : Prop :=
  forall k, LinearTimeStringMap.get k d1 = LogTimeStringMap.get k d2.

Lemma upgrade_establishes_simulation :
  forall d1,
    simulation d1 (upgrade d1).
Proof.
  unfold simulation.
  eauto using LT.list_to_tree_equiv.
Qed.

Lemma set_preserves_simulation :
  forall d1 d2 k v,
    simulation d1 d2 ->
    simulation (VarD.LinearTimeVarD.Map.set k v d1) (VarD.LogTimeVarD.Map.set k v d2).
Proof.
  unfold simulation.
  intros.
  rewrite LinearTimeStringMap.gsspec, LogTimeStringMap.gsspec.
  unfold LinearTimeStringMap.elt_eq, LogTimeStringMap.elt_eq.
  unfold IndexedString.eq, EqString.eq.
  break_if; auto.
Qed.

Lemma remove_preserves_simulation :
  forall d1 d2 k,
    simulation d1 d2 ->
    simulation (VarD.LinearTimeVarD.Map.remove k d1) (VarD.LogTimeVarD.Map.remove k d2).
Proof.
  unfold simulation.
  intros.
  rewrite LinearTimeStringMap.grspec, LogTimeStringMap.grspec.
  unfold LinearTimeStringMap.elt_eq, LogTimeStringMap.elt_eq.
  unfold IndexedString.eq, EqString.eq.
  break_if; auto.
Qed.

Lemma simulation_get :
  forall d1 d2 k,
    simulation d1 d2 ->
    VarD.LinearTimeVarD.Map.get k d1 = VarD.LogTimeVarD.Map.get k d2.
Proof.
  auto.
Qed.

Theorem handlers_preserve_simulation :
  forall d1 d2 d1' i o,
    simulation d1 d2 ->
    LinearTimeVarD.VarDHandler i d1 = (o, d1') ->
    exists d2',
      simulation d1' d2' /\
      LogTimeVarD.VarDHandler i d2 = (o, d2').
Proof.
  destruct i eqn:?; simpl; intros;
    unfold StateMachineHandlerMonad.bind in *; repeat break_let; repeat find_inversion.
  - unfold LinearTimeVarD.resp, LogTimeVarD.resp in *.
    unfold LinearTimeVarD.setk, LogTimeVarD.setk in *.
    unfold LinearTimeVarD.getk, LogTimeVarD.getk in *.
    StateMachineHandlerMonad.monad_unfold.
    repeat find_inversion.
    eexists. intuition eauto using f_equal2.
    auto using set_preserves_simulation.
  - unfold LinearTimeVarD.resp, LogTimeVarD.resp in *.
    unfold LinearTimeVarD.setk, LogTimeVarD.setk in *.
    unfold LinearTimeVarD.getk, LogTimeVarD.getk in *.
    StateMachineHandlerMonad.monad_unfold.
    repeat find_inversion.
    eauto using f_equal2.
  - unfold LinearTimeVarD.resp, LogTimeVarD.resp in *.
    unfold LinearTimeVarD.delk, LogTimeVarD.delk in *.
    unfold LinearTimeVarD.getk, LogTimeVarD.getk in *.
    StateMachineHandlerMonad.monad_unfold.
    repeat find_inversion.
    eexists. intuition eauto using f_equal2.
    auto using remove_preserves_simulation.
  - unfold LinearTimeVarD.resp, LogTimeVarD.resp in *.
    unfold LinearTimeVarD.setk, LogTimeVarD.setk in *.
    unfold LinearTimeVarD.getk, LogTimeVarD.getk in *.
    StateMachineHandlerMonad.monad_unfold.
    repeat find_inversion.
    erewrite simulation_get in * by eauto.
    repeat break_if; try congruence; repeat find_inversion;
    eexists; intuition eauto using f_equal2;
    eauto using set_preserves_simulation.
  - unfold LinearTimeVarD.resp, LogTimeVarD.resp in *.
    unfold LinearTimeVarD.delk, LogTimeVarD.delk in *.
    unfold LinearTimeVarD.getk, LogTimeVarD.getk in *.
    StateMachineHandlerMonad.monad_unfold.
    repeat find_inversion.
    erewrite simulation_get in * by eauto.
    repeat break_if; try congruence; repeat find_inversion;
    eexists; intuition eauto using f_equal2;
    eauto using remove_preserves_simulation.
Qed.

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