Require Import Verdi.Verdi.
Require Import Verdi.Disk.

Require Import Cheerios.Cheerios.

Section DiskCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {data_serializer : Serializer data}.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.

  Definition disk_packet := @d_packet _ disk_params.
  Definition disk_network := @d_network _ disk_params.

  Definition revertPacket (p : disk_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (d_pSrc p) (d_pDst p) (d_pBody p).

  Theorem revertPacket_src : forall p : disk_packet,
      d_pSrc p = pSrc (revertPacket p).
  Proof.
    reflexivity.
  Qed.

  Theorem revertPacket_dst : forall p : disk_packet,
      d_pDst p = pDst (revertPacket p).
  Proof.
    reflexivity.
  Qed.

  Theorem revertPacket_body : forall p : disk_packet,
      d_pBody p = pBody (revertPacket p).
  Proof.
    reflexivity.
  Qed.

  Definition revertDiskNetwork (net: disk_network) : orig_network :=
    mkNetwork (map revertPacket (nwdPackets net)) (nwdState net).

  Lemma  revertDiskNetwork_state :
    forall net, nwdState net = nwState (revertDiskNetwork net).
  Proof.
    reflexivity.
  Qed.

  Theorem revertDiskNetwork_packets : forall st l,
      nwdPackets st = l -> nwPackets (revertDiskNetwork st) = map revertPacket l.
  Proof.
    intros.
    simpl.
    find_rewrite.
    reflexivity.
  Qed.

  Theorem map_revertPacket : forall st,
      map revertPacket (nwdPackets st) = nwPackets (revertDiskNetwork st).
  Proof.
    reflexivity.
  Qed.

  Theorem revert_d_send_packets : forall h l,
      map revertPacket (d_send_packets h l) =
      send_packets h l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - break_exists.
      simpl map.
      find_rewrite.
      reflexivity.
  Qed.

  Lemma reachable_revert_step :
    forall st st' out,
      reachable step_async_disk step_async_disk_init st ->
      step_async_disk st st' out ->
      (exists out, step_async (revertDiskNetwork st) (revertDiskNetwork st') out).
  Proof using.
    intros.
    unfold reachable in *.
    break_exists.
    match goal with H : step_async_disk _ _ _ |- _ => invc H end.
    - match goal with H : d_net_handlers _ _ _ _ = _ |- _ => simpl in H end.
      unfold disk_net_handlers in *.
      repeat break_match.
      simpl d_name_eq_dec.
      rewrite revertPacket_src, revertPacket_dst, revertPacket_body, revertDiskNetwork_state in *.
      copy_apply revertDiskNetwork_packets H1.
      unfold revertDiskNetwork at 2.
      unfold nwdPackets, nwdState.

      assert (p :: ys = [p] ++ ys). reflexivity.
      repeat find_rewrite.
      repeat rewrite map_app in *.

      rewrite revert_d_send_packets.
      exists [(pDst (revertPacket p), inr out0)].
      apply (@StepAsync_deliver orig_base_params orig_multi_params _ _ _ (map revertPacket xs) (map revertPacket ys) _ d l).
      + assumption.
      + find_inversion.
        assumption.
      + reflexivity.
    - match goal with H : d_input_handlers _ _ _ = _ |- _ => invc H end.
      unfold disk_input_handlers in *.
      repeat break_match.
      simpl d_name_eq_dec.
      rewrite revertDiskNetwork_state in *.
      unfold revertDiskNetwork at 2.
      unfold nwdPackets at 1, nwdState.
      rewrite map_app.
      exists [(h, inl inp); (h, inr out0)].
      rewrite map_revertPacket.
      rewrite revert_d_send_packets.
      apply (@StepAsync_input _ orig_multi_params _ _ _ _ _ d l).
      + find_inversion.
        assumption.
      + reflexivity.
  Qed.

  Theorem reachable_revert :
    true_in_reachable step_async_disk step_async_disk_init
                      (fun (st : disk_network) =>
                         reachable step_async
                                   step_async_init
                                   (revertDiskNetwork st)).
  Proof.
    apply true_in_reachable_reqs.
    - unfold revertDiskNetwork. simpl.
      unfold reachable. exists []. constructor.
    - intros.
      find_apply_lem_hyp reachable_revert_step; auto.
      intuition.
      unfold reachable in *.
      break_exists.
      eexists.
      apply refl_trans_n1_1n_trace.
      econstructor; eauto using refl_trans_1n_n1_trace.
  Qed.

  Theorem true_in_reachable_disk_transform :
    forall P,
      true_in_reachable step_async step_async_init P ->
      true_in_reachable step_async_disk step_async_disk_init (fun net => P (revertDiskNetwork net)).
  Proof.
    intros. find_apply_lem_hyp true_in_reachable_elim. intuition.
    apply true_in_reachable_reqs. eauto.
    intros. find_copy_apply_lem_hyp reachable_revert.
    find_apply_lem_hyp reachable_revert_step; auto.
    intuition.
    break_exists.
    eauto.
  Qed.
End DiskCorrect.
