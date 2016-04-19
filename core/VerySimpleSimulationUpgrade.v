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
      step_f_star step_f_init net tr ->
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
      simulation sigma1 sigma2 ->
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

  Lemma lifted_stutter_step :
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
    - unfold lifted_net in *. simpl. intuition.
      exists failed.
      match goal with
      | |- context [?pkts = map lift_packet _] =>
        remember (map lower_packet pkts) as lowered_packets
      end.
      remember (Net.nwState net_f) as lowered_state.
      exists {| Net.nwPackets := lowered_packets; Net.nwState := lowered_state |}.
      intuition.
      + right. subst.
        map_crush.
        repeat find_rewrite.
        apply SF_drop with (xs0 := map lower_packet xs)
                             (p0 := lower_packet p)
                             (ys0 := map lower_packet ys); auto.
        change (lower_packet p :: map lower_packet ys) with
               (map lower_packet (p :: ys)).
        rewrite <- map_app.
        find_rewrite. apply map_lower_lift.
      + subst. simpl.
        apply map_lift_lower.
    - unfold lifted_net in *. simpl. intuition.
      exists failed.
      match goal with
      | |- context [?pkts = map lift_packet _] =>
        remember (map lower_packet pkts) as lowered_packets
      end.
      remember (Net.nwState net_f) as lowered_state.
      exists {| Net.nwPackets := lowered_packets; Net.nwState := lowered_state |}.
      intuition.
      + right. subst.
        map_crush.
        repeat find_rewrite.
        apply SF_dup with (xs0 := map lower_packet xs)
                             (p0 := lower_packet p)
                             (ys0 := map lower_packet ys).
        * change (lower_packet p :: map lower_packet ys) with
                 (map lower_packet (p :: ys)).
          rewrite <- map_app.
          find_rewrite. apply map_lower_lift.
        * f_equal.
          f_equal.
          change (lower_packet p :: map lower_packet ys) with
                 (map lower_packet (p :: ys)).
          rewrite <- map_app.
          find_rewrite. auto.
      + subst. simpl.
        apply map_lift_lower.
    - exists (h :: failed). exists net_f.
      intuition; eauto using SF_fail.
      unfold lifted_net in *.
      simpl. intuition congruence.
    - {
        exists (remove name_eq_dec h failed).
        unfold reboot. repeat break_match.
        - unfold lifted_net in *.
          intuition.
          exists {| Net.nwPackets := Net.nwPackets net_f;
               Net.nwState := update (Net.nwState net_f) h (reboot1 d) |}.
          simpl. intuition; repeat find_rewrite; auto.
          + repeat find_rewrite. subst.
            right. apply SF_reboot with (h0 := h); auto.
            f_equal.
            unfold update.
            apply functional_extensionality.
            intros.
            repeat break_if; subst; try congruence.
            simpl.
            f_equal.
            unfold lifted_state in *.
            intuition.
            find_insterU; intuition; rewrite Heqs in *;
              [find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; eauto using version_eq_dec|].
            break_exists; intuition; congruence.
          + unfold lifted_state.
            intros. unfold update.
            break_if; auto.
        - subst.
          unfold lifted_net in *. intuition. simpl in *.
          match goal with
          | H : context [lifted_state] |- _ =>
            pose proof H;
            specialize (H h)
          end.
          intuition; repeat find_rewrite; try congruence.
          break_exists. intuition.
          find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; eauto using version_eq_dec.
          subst.
          exists {| Net.nwPackets := Net.nwPackets net_f;
               Net.nwState := update (Net.nwState net_f) h (reboot1 (Net.nwState net_f h)) |}.
          simpl. intuition.
          + right.
            eapply SF_reboot with (h0 := h); auto.
            f_equal.
            unfold update. apply functional_extensionality.
            intros. repeat break_if; subst; auto; congruence.
          + unfold lifted_state.
            intros. unfold update. break_if; subst; auto.
            right.
            find_eapply_lem_hyp reboot_preserves_upgrade; eauto.
            break_exists_exists. intuition. subst. auto.
      }
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
  Qed.

  Theorem lifted_step_star :
    forall net_u net_u' failed net_f tr,
      lifted_net failed net_f net_u ->
      step_u_star net_u net_u' tr ->
      exists failed' net_f',
        step_f_star (failed, net_f) (failed', net_f') tr /\
        lifted_net failed' net_f' net_u'.
  Proof.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    match goal with
    | H : context [step_u] |- _ => induction H
    end.
    - exists failed, net_f. intuition.
      constructor.
    - intuition.
      break_exists. intuition.
      find_eapply_lem_hyp lifted_stutter_step; eauto.
      break_exists_exists. intuition; subst; try rewrite app_nil_r; eauto.
      find_apply_lem_hyp refl_trans_1n_n1_trace.
      apply refl_trans_n1_1n_trace.
      now econstructor; eauto.
  Qed.

  Lemma lifted_step_f_init :
    lifted_net (fst step_f_init) (snd step_f_init) step_u_init.
  Proof.
    unfold lifted_net. intuition; simpl in *; auto.
    unfold lifted_state. intuition.
  Qed.

  Theorem step_u_step_f :
    forall net_u' tr,
      step_u_star step_u_init net_u' tr ->
      exists failed' net_f',
        step_f_star step_f_init (failed', net_f') tr.
  Proof.
    intros.
    pose proof lifted_step_f_init.
    unfold step_f_init in *. simpl in *.
    find_eapply_lem_hyp lifted_step_star; eauto.
    break_exists_exists; intuition.
  Qed.

  Theorem trace_prop_step_u :
    forall net_u' tr,
      step_u_star step_u_init net_u' tr ->
      trace_prop tr.
  Proof.
    intros.
    find_apply_lem_hyp step_u_step_f.
    break_exists.
    eauto using trace_prop_invariant.
  Qed.
      
End VerySimpleSimulationUpgrade.