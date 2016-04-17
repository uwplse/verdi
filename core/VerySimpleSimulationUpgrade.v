Require Import List.
Require Import Verdi.
Require Import UpgradeNet.

Section FirstProjection.
  Context `{params : VerySimpleUpgradeParams}.

  Global Instance first_projection_base : BaseParams :=
    {
      data := data1;
      input := input;
      output := output
    }.

  Global Instance first_projection_multi : MultiParams first_projection_base :=
    {
      name := name;
      msg := msg;
      msg_eq_dec := msg_eq_dec;
      name_eq_dec := name_eq_dec;
      nodes := nodes;
      all_names_nodes := all_names_nodes;
      no_dup_nodes := no_dup_nodes;
      init_handlers := init_handlers;
      net_handlers := net_handlers1;
      input_handlers := input_handlers1
    }.

  Global Instance first_projection_failure :
    FailureParams first_projection_multi :=
    {
      reboot := reboot1
    }.
  
End FirstProjection.


Section VerySimpleSimulationUpgrade.
  Context `{params : VerySimpleUpgradeParams}.

  Variable trace_prop : list (name * (input + list output)) -> Prop.
  Variable trace_prop_invariant :
    forall net tr,
      step_f step_f_init net tr ->
      trace_prop tr.

  Variable input_preserves_upgrade :
    forall h inp sigma sigma' os ms,
      input_handlers1 h inp sigma = (os, sigma', ms) ->
      input_handlers2 h inp (upgrade sigma) = (os, upgrade sigma', ms).

  Variable net_preserves_upgrade :
    forall h h' p sigma sigma' os ms,
      net_handlers1 h h' p sigma = (os, sigma', ms) ->
      net_handlers2 h h' p (upgrade sigma) = (os, upgrade sigma', ms).

  Variable reboot_preserves_upgrade :
    forall sigma sigma',
      reboot1 sigma = sigma' ->
      reboot2 (upgrade sigma) = (upgrade sigma').

  Definition lifted_state (sigma : name -> data1) (sigma' : name -> sigT data) : Prop :=
    forall h,
      sigma' h = existT _ One (sigma h) \/
      sigma' h = existT _ Two (upgrade (sigma h)).

  Definition lift_packet (p : Net.packet) : packet :=
    {| pSrc := Net.pSrc p ;
       pDst := Net.pDst p ;
       pBody := Net.pBody p|}.

  Definition lower_packet (p : packet) : Net.packet :=
    {| Net.pSrc := pSrc p ;
       Net.pDst := pDst p ;
       Net.pBody := pBody p|}.
  
  Definition lifted_net (failed : list name) (net : @Net.network _ first_projection_multi) (net' : network) :=
    nwFailed net' = failed /\
    nwPackets net' = map lift_packet (Net.nwPackets net) /\
    lifted_state (Net.nwState net) (nwState net').
                     

  Theorem trace_prop_invariant_upgrade_one :
    forall net_u net_u' failed net_f tr,
      lifted_net failed net_f net_u ->
      step_u net_u net_u' tr ->
      exists failed' net_f',
        step_f (failed, net_f) (failed', net_f') tr /\
        lifted_net failed' net_f' net_u'.
  Proof.
    intros. invcs H0.
    - (exists failed).
      remember (lower_packet p) as p'.
      assert (pDst p = Net.pDst p') by
          (subst; simpl; auto).
      rewrite H0.
      eexists; intuition eauto.
      econstructor 1.
  Admitted.
  
End VerySimpleSimulationUpgrade.