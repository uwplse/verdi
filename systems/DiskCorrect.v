Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.

Require Import Verdi.Disk.

Require Import mathcomp.ssreflect.ssreflect.

Section DiskCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {data_serializer : Serializer data}.

  Lemma disk_follows_local_state: forall net tr,
      step_async_disk_star step_async_disk_init net tr ->
      forall n, @d_reboot _ _ disk_failure_params (nwdDisk net n) = Some (nwdState net n).
  Proof.
    intros.
    remember step_async_disk_init as y in *.
    revert Heqy.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - simpl.
      unfold init_handlers.
      apply serialize_deserialize_top_id.
    - concludes.
      match goal with
      | [ H : step_async_disk _ _ _ |- _ ] => invc H
      end; simpl;
        break_if;
        try assumption;
        simpl in *; unfold disk_net_handlers, disk_input_handlers in *;
          repeat break_match;
          repeat find_inversion;
          apply serialize_deserialize_top_id.
  Qed.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.

  Definition disk_packet := @d_packet _ disk_params.
  Definition disk_network := @d_network _ disk_params.

  Definition revertPacket (p : disk_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (d_pSrc p) (d_pDst p) (d_pBody p).

  Definition revertDiskNetwork (net: disk_network) : orig_network :=
    mkNetwork (map revertPacket (nwdPackets net)) (nwdState net).

  Lemma step_async_disk_star_step :
    forall net net' tr,
      step_async_disk net net' tr ->
      step_async (revertDiskNetwork net) (revertDiskNetwork net') tr.
  Proof.
    move => net net' tr H_step.
    destruct H_step.
    - subst.
      rewrite /= /revertDiskNetwork /= 2!map_app /=.
      rewrite /d_net_handlers /= /disk_net_handlers /= in H0.
      repeat break_let.
      find_inversion.
      have ->: d_pDst p = pDst (revertPacket p) by [].
      eapply StepAsync_deliver; eauto.
      * by rewrite /= H map_app /=; eauto.
      * rewrite /d_send_packets /=.
        set p1 := map revertPacket _.
        set p2 := map _ l.
        suff H_suff: p1 = p2 by rewrite H_suff.
        rewrite /p1 /p2 {p1 p2 Heqp0}.
        elim: l => //=.
        case => n m l IH.
        by rewrite {1}/revertPacket /= IH.
    - subst.
      rewrite /= /revertDiskNetwork /= map_app.
      rewrite /d_input_handlers /= /disk_input_handlers /= in H.
      repeat break_let.
      find_inversion.
      eapply StepAsync_input; eauto.
      rewrite /=.
      set p1 := map revertPacket _.
      set p2 := map _ l.
      suff H_suff: p1 = p2 by rewrite H_suff.
      rewrite /p1 /p2 {p1 p2 Heqp}.
      elim: l => //=.
      case => n m l IH.
      by rewrite {1}/revertPacket /= IH.
  Qed.

  Lemma step_async_disk_star_revert_simulation : 
    forall net tr,
      step_async_disk_star step_async_disk_init net tr ->
      step_async_star step_async_init (revertDiskNetwork net) tr.
  Proof.   
  Admitted.

  Corollary true_in_reachable_disk_transform :
    forall P,
      true_in_reachable step_async step_async_init P ->
      true_in_reachable step_async_disk step_async_disk_init (fun net => P (revertDiskNetwork net)).
  Proof.
    rewrite /true_in_reachable /reachable => P H_r net H_r'.
    break_exists.
    find_apply_lem_hyp step_async_disk_star_revert_simulation.
    apply H_r.
    by exists x.
  Qed.
End DiskCorrect.
