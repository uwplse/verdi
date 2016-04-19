Require Import Raft.
Require Import Net.
Require Import StateMachineUpgrade.

Section Projections.
  Context `{params : StateMachineUpgradeParams}.

  Global Instance first_projection_base : BaseParams :=
    {
      data := data1;
      input := input;
      output := output
    }.

  Global Instance first_projection_one_node : OneNodeParams first_projection_base :=
    {
      init := init;
      handler := input_handlers1
    }.

  Global Instance second_projection_base : BaseParams :=
    {
      data := data2;
      input := input;
      output := output
    }.

  Global Instance second_projection_one_node : OneNodeParams second_projection_base :=
    {
      init := (upgrade init);
      handler := input_handlers2
    }.
End Projections.

Require Import UpgradeNet.

Section Combine.
  Variable base_params1 : BaseParams.
  Variable multi_params1 : MultiParams base_params1.
  Variable failure_params1 : FailureParams multi_params1.

  Variable base_params2 : BaseParams.
  Variable multi_params2 : MultiParams base_params2.
  Variable failure_params2 : FailureParams multi_params2.

  Variable upgrade : (@Net.data base_params1) -> (@Net.data base_params2).

  Variable input_eq : (@Net.input base_params1) = (@Net.input base_params2).
  Variable output_eq : (@Net.output base_params1) = (@Net.output base_params2).
  Variable name_eq : (@Net.name _ multi_params1) = (@Net.name _ multi_params2).
  Variable msg_eq : (@Net.msg _ multi_params1) = (@Net.msg _ multi_params2).

  Global Instance combined : VerySimpleUpgradeParams :=
    { name := (@Net.name _ multi_params1);
      msg :=  (@Net.msg _ multi_params1);
      input := (@Net.input base_params1);
      output := (@Net.output base_params1);
      msg_eq_dec := (@Net.msg_eq_dec _ multi_params1);
      name_eq_dec := (@Net.name_eq_dec _ multi_params1);
      nodes := (@Net.nodes _ multi_params1);
      all_names_nodes := (@Net.all_names_nodes _ multi_params1);
      no_dup_nodes := (@Net.no_dup_nodes _ multi_params1);
      data1 := (@Net.data base_params1);
      init_handlers := (@Net.init_handlers _ multi_params1);
      net_handlers1 := (@Net.net_handlers _ multi_params1);
      input_handlers1 := (@Net.input_handlers _ multi_params1);
      reboot1 := (@Net.reboot _ _ failure_params1);
      data2 := (@Net.data base_params2);
      reboot2 := (@Net.reboot _ _ failure_params2);
      upgrade := upgrade
    }.
  Proof.
    - pose (@Net.net_handlers _ multi_params2) as h.
      repeat find_rewrite.
      apply h.
    - pose (@Net.input_handlers _ multi_params2) as h.
      repeat find_rewrite.
      apply h.
  Defined.

  (*
  Require Import VerySimpleSimulationUpgrade.
  Lemma projection_eq :
    first_projection_base = base_params1.
  Proof.
    Set Printing All. idtac.
    unfold combined. unfold first_projection_base.
    simpl. destruct base_params1.
    simpl. auto.
  Qed.
   *)
End Combine.
  
Section RaftLiftsSimulation.
  Context `{SMU_params : StateMachineUpgradeParams}.
  Context `{raft_params : @RaftParams first_projection_base}.

  Variable simulation : StateMachineUpgrade.data1 -> StateMachineUpgrade.data2 -> Prop.

  Variable upgrade_establishes_simulation :
    forall sigma,
      simulation sigma (StateMachineUpgrade.upgrade sigma).

  Variable handlers_preserve_simulation :
    forall d1 d2 d1' i o,
      simulation d1 d2 ->
      StateMachineUpgrade.input_handlers1 i d1 = (o, d1') ->
      exists d2',
        simulation d1' d2' /\
        StateMachineUpgrade.input_handlers2 i d2 = (o, d2').
  
End RaftLiftsSimulation.
  