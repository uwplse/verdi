Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.
Require Import FunctionalExtensionality.

Require Import Verdi.Disk.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Section DiskCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {data_serializer : Serializer data}.

  Hypothesis reboot_idem : forall d, reboot (reboot d) = reboot d.

  Lemma disk_deserialize_some : forall net failed tr,
      step_failure_disk_star step_failure_disk_init (failed, net) tr ->
      forall n, exists d, deserialize_top deserialize (nwdDisk net n) = Some d.
  Proof.
    remember step_failure_disk_init as y in *.
    move => net failed tr H_st.
    change net with (snd (failed, net)).
    move: Heqy.
    induction H_st using refl_trans_1n_trace_n1_ind => H_eq n.
    - rewrite H_eq /= /init_disk /=.
      rewrite serialize_deserialize_top_id.
      by exists (init_handlers n).
    - concludes.
      match goal with
      | [ H : step_failure_disk _ _ _ |- _ ] => invcs H
      end; simpl => //.
      * break_if => //.
        subst.
        unfold disk_net_handlers in *.
        repeat break_let.
        find_inversion.
        rewrite serialize_deserialize_top_id.
        by exists d.
      * break_if => //.
        subst.
        unfold disk_input_handlers in *.
        repeat break_let.
        find_inversion.
        rewrite serialize_deserialize_top_id.
        by exists d.
   Qed.

  Lemma disk_follows_local_state_reboot : forall net failed tr,
      step_failure_disk_star step_failure_disk_init (failed, net) tr ->
      forall n d, deserialize_top deserialize (nwdDisk net n) = Some d ->
        reboot d = reboot (nwdState net n).
  Proof.
    remember step_failure_disk_init as y in *.
    move => net failed tr H_st.
    change net with (snd (failed, net)).
    move: Heqy.
    induction H_st using refl_trans_1n_trace_n1_ind => 
    H_init n d; first by rewrite H_init /= /init_disk serialize_deserialize_top_id => H_d; find_injection.
    concludes.
    match goal with
      | [ H : step_failure_disk _ _ _ |- _ ] => invcs H
    end; simpl => //.
    - unfold disk_net_handlers in *.
      repeat break_let.
      find_inversion.
      break_if.
      * subst. rewrite serialize_deserialize_top_id => H_d.
        by find_injection.
      * exact: IHH_st1.
   - unfold disk_input_handlers in *.
     repeat break_let.
     find_inversion.
     break_if.
     * subst. rewrite serialize_deserialize_top_id => H_d.
       by find_injection.
     * exact: IHH_st1.
   - exact: IHH_st1.
   - exact: IHH_st1.
   - exact: IHH_st1.
   - break_if.
     * subst.
       break_match => //.
       + move => H_eq.
         rewrite Heqo in H_eq.
         find_injection.
         by rewrite reboot_idem.
       + move => H_eq.
         rewrite Heqo in H_eq.
         by congruence.
       + exact: IHH_st1.
   Qed.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.

  Definition disk_packet := @d_packet _ disk_multi_params.
  Definition disk_network := @d_network _ disk_multi_params.

  Definition revertPacket (p : disk_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (d_pSrc p) (d_pDst p) (d_pBody p).

  Definition revertDiskNetwork (net: disk_network) : orig_network :=
    mkNetwork (map revertPacket (nwdPackets net)) (nwdState net).

  Theorem disk_step_failure_step :
    forall net net' failed failed' tr tr',
      step_failure_disk_star step_failure_disk_init (failed, net) tr ->
      step_failure_disk (failed, net) (failed', net') tr' ->
      step_failure (failed, revertDiskNetwork net) (failed', revertDiskNetwork net') tr'.
  Proof.
    move => net net' failed failed' tr tr' H_star H_step.
    invcs H_step.
    - rewrite /= /revertDiskNetwork /= 2!map_app /=.
      rewrite /d_net_handlers /= /disk_net_handlers /= in H6.
      repeat break_let.
      find_inversion.
      have ->: d_pDst p = pDst (revertPacket p) by [].
      eapply StepFailure_deliver; eauto.
      * by rewrite /= H3 map_app /=; eauto.
      * rewrite /d_send_packets /=.
        set p1 := map revertPacket _.
        set p2 := map _ l.
        suff H_suff: p1 = p2 by rewrite H_suff.
        rewrite /p1 /p2 {p1 p2 Heqp0}.
        elim: l => //=.
        case => n m l IH.
        by rewrite {1}/revertPacket /= IH.
    - rewrite /= /revertDiskNetwork /= map_app.
      rewrite /d_input_handlers /= /disk_input_handlers /= in H5.
      repeat break_let.
      find_inversion.
      eapply StepFailure_input; eauto.
      rewrite /=.
      set p1 := map revertPacket _.
      set p2 := map _ l.
      suff H_suff: p1 = p2 by rewrite H_suff.
      rewrite /p1 /p2 {p1 p2 Heqp}.
      elim: l => //=.
      case => n m l IH.
      by rewrite {1}/revertPacket /= IH.
    - rewrite /= /revertDiskNetwork /= map_app.
      eapply StepFailure_drop; eauto.
      rewrite /= H4 map_app /=.
      by eauto.
    - rewrite /= /revertDiskNetwork /= map_app.
      eapply StepFailure_dup; eauto => //=.
      by rewrite H4 map_app.
    - exact: StepFailure_fail.
    - rewrite /revertDiskNetwork /=.
      eapply StepFailure_reboot; eauto.
      rewrite /=.
      set s1 := fun _ => _.
      set s2 := fun _ => _.
      suff H_suff: s1 = s2 by rewrite H_suff.
      rewrite /s1 /s2 {s1 s2}.
      apply functional_extensionality => n.
      break_if => //=.
      subst.
      break_match.
      * exact: disk_follows_local_state_reboot _ _ _ H_star h _ Heqo.
      * have H_st' := disk_deserialize_some _ _ _ H_star h.
        break_exists.
        rewrite H in Heqo.
        by congruence.
  Qed.

  Lemma disk_step_failure_star_simulation :
    forall net failed tr,
      step_failure_disk_star step_failure_disk_init (failed, net) tr ->
      step_failure_star step_failure_init (failed, revertDiskNetwork net) tr.
  Proof.
    move => net failed tr H_star.
    remember step_failure_disk_init as y in *.
    change failed with (fst (failed, net)).
    change net with (snd (failed, net)) at 2.
    move: Heqy.
    induction H_star using refl_trans_1n_trace_n1_ind => H_init.
    - find_rewrite.
      rewrite /= /revertDiskNetwork /=.
      by constructor.
    - concludes.
      destruct x' as (failed', net').
      destruct x'' as (failed'', net'').
      subst.
      apply RT1n_step with (y := (failed', revertDiskNetwork net')).
      + exact: IHH_star1.
      + exact: (disk_step_failure_step _ _ _ _ tr1).
  Qed.

  Corollary true_in_reachable_disk_transform :
    forall P,
      true_in_reachable step_failure step_failure_init P ->
      true_in_reachable step_failure_disk step_failure_disk_init (fun st => P (fst st, revertDiskNetwork (snd st))).
  Proof.
    rewrite /true_in_reachable /reachable => P H_r [failed net] H_r'.
    break_exists.
    find_apply_lem_hyp disk_step_failure_star_simulation.
    apply H_r.
    by exists x.
  Qed.
End DiskCorrect.
