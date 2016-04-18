Require Import List.
Require Import Verdi.
Require Import UpgradeNet.
Require Import FunctionalExtensionality.

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

  Variable simulation :
    data1 -> data2 -> Prop.

  Variable upgrade_establishes_simulation :
    forall sigma,
      simulation sigma (upgrade sigma).

  Variable input_preserves_upgrade :
    forall h inp sigma1 sigma2 sigma1' os ms,
      simulation sigma1 sigma2 ->
      input_handlers1 h inp sigma1 = (os, sigma1', ms) ->
      exists sigma2',
        simulation sigma1' sigma2' /\
        input_handlers2 h inp sigma2 = (os, sigma2', ms).

  Variable net_preserves_upgrade :
    forall h h' p sigma1 sigma1' sigma2 os ms,
      simulation sigma1 sigma2 ->
      net_handlers1 h h' p sigma1 = (os, sigma1', ms) ->
      exists sigma2',
        simulation sigma1' sigma2' /\
        net_handlers2 h h' p sigma2 = (os, sigma2', ms).

  Variable reboot_preserves_upgrade :
    forall sigma1 sigma1' sigma2,
      reboot1 sigma1 = sigma1' ->
      exists sigma2',
        simulation sigma1' sigma2' /\
        reboot2 sigma2 = sigma2'.

  Definition lifted_state (sigma : name -> data1) (sigma' : name -> sigT data) : Prop :=
    forall h,
      sigma' h = existT _ One (sigma h) \/
      exists sigma2,
        simulation (sigma h) sigma2 /\
        sigma' h = existT _ Two sigma2.

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

  Lemma lift_packet_lower_packet_inverses_1 :
    forall p,
      lift_packet (lower_packet p) = p.
  Proof.
    intros.
    unfold lift_packet, lower_packet.
    destruct p. reflexivity.
  Qed.

  Lemma lift_packet_lower_packet_inverses_2 :
    forall p,
      lower_packet (lift_packet p) = p.
  Proof.
    intros.
    unfold lift_packet, lower_packet.
    destruct p. reflexivity.
  Qed.

  Lemma map_lift_lower :
    forall l,
      l = map lift_packet (map lower_packet l).
  Proof.
    intros.
    rewrite map_map.
    rewrite map_ext with (g := id);
      eauto using map_id, lift_packet_lower_packet_inverses_1.
  Qed.

  Lemma map_lower_lift :
    forall l,
      l = map lower_packet (map lift_packet l).
  Proof.
    intros.
    rewrite map_map.
    rewrite map_ext with (g := id);
      eauto using map_id, lift_packet_lower_packet_inverses_2.
  Qed.

  Lemma version_eq_dec :
    forall x y : version,
      {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  Theorem trace_prop_invariant_upgrade_one :
    forall net_u net_u' failed net_f tr,
      lifted_net failed net_f net_u ->
      step_u net_u net_u' tr ->
      exists failed' net_f',
        ((failed = failed' /\ net_f = net_f' /\ tr = []) \/
         step_f (failed, net_f) (failed', net_f') tr) /\
        lifted_net failed' net_f' net_u'.
  Proof.
    intros. invcs H0.
    - (exists failed).
      remember (lower_packet p) as p'.
      assert (pDst p = Net.pDst p') by
          (subst; simpl; auto).
      rewrite H0.
      unfold net_handlers in *.
      repeat break_match.
      + {
          - remember (Net.update (Net.nwState net_f) (Net.pDst p') d1) as lowered_state.
            match goal with
            | |- context [{| nwFailed := _; nwState := _;
                            nwPackets := ?pkts |}] =>
              remember (map lower_packet pkts) as lowered_packets
            end.
            exists {| Net.nwPackets := lowered_packets; Net.nwState := lowered_state |}.
            subst. 
            intuition.
            + right. assert (Net.nwState net_f (pDst p) = d0).
              {
                unfold lifted_net, lifted_state in *. intuition.
                find_insterU; intuition; erewrite Heqs in *; find_inversion.
                find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; eauto using version_eq_dec.
                break_exists. intuition. congruence.
              }
              subst. find_inversion.
              eapply SF_deliver with (xs0 := map lower_packet xs) (ys0 := map lower_packet ys);
                simpl in *; eauto.
              * unfold lifted_net in *. intuition. repeat find_rewrite.
                change (lower_packet p :: map lower_packet ys) with
                (map lower_packet (p :: ys)).
                rewrite <- map_app.
                find_rewrite. apply map_lower_lift.
              * unfold lifted_net in *. intuition congruence.
              * f_equal. unfold send_packets.
                map_crush. unfold lower_packet. simpl in *. auto.
            + unfold lifted_net in *; intuition; simpl in *;
                eauto using map_lift_lower.
              find_inversion.
              unfold update.
              unfold lifted_state.
              intros. break_if; auto.
        }
      + {
          - find_inversion.
            unfold lifted_net in *. intuition.
            pose proof H5 (pDst p).
            intuition; try congruence.
            break_exists_name sigma2; intuition; repeat find_rewrite.
            find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; eauto using version_eq_dec; subst d0.
            match goal with
            | _ : net_handlers2 ?dst ?src ?body ?s2 = _,
                  _ : simulation ?s1 ?s2
              |- _ =>
              destruct (net_handlers1 dst src body s1) eqn:?
            end.
            match goal with
            | H : net_handlers1 _ _ _ ?s1 = (?x, _),
                  _ : simulation ?s1 ?s2
              |- _ =>
              destruct x; copy_eapply net_preserves_upgrade H; eauto
            end.
            break_exists_name sigma2'. intuition; repeat find_rewrite.
            find_inversion. simpl.
            remember (Net.update (Net.nwState net_f) (Net.pDst (lower_packet p)) d) as lowered_state.
            match goal with
            | |- context [?pkts = map lift_packet _] =>
              remember (map lower_packet pkts) as lowered_packets
            end.
            exists {| Net.nwPackets := lowered_packets; Net.nwState := lowered_state |}.
            subst.
            intuition.
            + right. repeat find_rewrite.
              eapply SF_deliver with (xs0 := map lower_packet xs) (ys0 := map lower_packet ys);
                simpl in *; eauto.
              * change (lower_packet p :: map lower_packet ys) with
                (map lower_packet (p :: ys)).
                rewrite <- map_app.
                find_rewrite. apply map_lower_lift.
              * f_equal. unfold send_packets.
                map_crush. reflexivity.
            + unfold lifted_net in *; intuition; simpl in *;
                eauto using map_lift_lower.
            + simpl.
              unfold update.
              unfold lifted_state. intros.
              break_if; auto.
              right. eexists; intuition eauto.
        }
    - (exists failed).
      unfold input_handlers in *.
      repeat break_match.
      + {
          - remember (Net.update (Net.nwState net_f) h d1) as lowered_state.
            match goal with
            | |- context [{| nwFailed := _; nwState := _;
                            nwPackets := ?pkts |}] =>
              remember (map lower_packet pkts) as lowered_packets
            end.
            exists {| Net.nwPackets := lowered_packets; Net.nwState := lowered_state |}.
            subst. 
            intuition.
            + right. assert (Net.nwState net_f h = d0).
              {
                unfold lifted_net, lifted_state in *. intuition.
                find_insterU; intuition; erewrite Heqs in *; find_inversion.
                find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; eauto using version_eq_dec.
                break_exists. intuition. congruence.
              }
              subst. find_inversion.
              eapply SF_input with (h0 := h);
                simpl in *; eauto.
              * unfold lifted_net in *. intuition congruence.
              * unfold lifted_net in *. intuition.
                repeat find_rewrite.
                f_equal. unfold send_packets.
                map_crush. f_equal.
                erewrite map_ext; try solve [apply map_id].
                intros. simpl. apply lift_packet_lower_packet_inverses_2.
            + unfold lifted_net in *; intuition; simpl in *;
                eauto using map_lift_lower.
              find_inversion.
              unfold update.
              unfold lifted_state.
              intros. break_if; auto.
        }
      + {
          - find_inversion.
            unfold lifted_net in *. intuition.
            pose proof H3 h.
            intuition; try congruence.
            break_exists_name sigma2; intuition; repeat find_rewrite.
            find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; eauto using version_eq_dec; subst d0.
            match goal with
            | _ : input_handlers2 ?dst ?inp ?s2 = _,
                  _ : simulation ?s1 ?s2
              |- _ =>
              destruct (input_handlers1 dst inp s1) eqn:?
            end.
            match goal with
            | H : input_handlers1 _ _ ?s1 = (?x, _),
                  _ : simulation ?s1 ?s2
              |- _ =>
              destruct x; copy_eapply input_preserves_upgrade H; eauto
            end.
            break_exists_name sigma2'. intuition; repeat find_rewrite.
            find_inversion. simpl.
            remember (Net.update (Net.nwState net_f) h d) as lowered_state.
            match goal with
            | |- context [?pkts = map lift_packet _] =>
              remember (map lower_packet pkts) as lowered_packets
            end.
            exists {| Net.nwPackets := lowered_packets; Net.nwState := lowered_state |}.
            subst.
            intuition.
            + right. repeat find_rewrite.
              eapply SF_input with (h0 := h);
                simpl in *; eauto.
              f_equal. unfold send_packets.
              map_crush. f_equal.
              erewrite map_ext; try solve [apply map_id].
              intros. simpl. apply lift_packet_lower_packet_inverses_2.
            + unfold lifted_net in *; intuition; simpl in *;
                eauto using map_lift_lower.
            + simpl.
              unfold update.
              unfold lifted_state. intros.
              break_if; auto.
              right. eexists; intuition eauto.
        }
    - admit.
    - admit.
    - admit.
    - admit.
    - exists failed, net_f. intuition.
      unfold upgrade_state.
      repeat break_match.
      + subst.
        unfold lifted_net in *. simpl. intuition.
        unfold lifted_state.
        intros. unfold update.
        break_if; subst; auto.
        right.
        exists (upgrade d); intuition.
        unfold lifted_state in *.
        match goal with
        | H : context [simulation] |- _ =>
          specialize (H h)
        end.
        intuition; repeat find_rewrite.
        * find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
            eauto using version_eq_dec.
          subst. eauto using upgrade_establishes_simulation.
        * break_exists. intuition. congruence.
      + match goal with
        | |- lifted_net _ _ ?net_u' =>
          assert (net_u' = net_u); repeat find_rewrite; auto
        end.
        destruct net_u.
        simpl.
        f_equal.
        apply functional_extensionality.
        intros.
        unfold update.
        break_if; subst; auto.
  Admitted.
  
End VerySimpleSimulationUpgrade.