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

  Definition revertDiskNetwork (net: disk_network) : orig_network :=
    mkNetwork (map revertPacket (nwdPackets net)) (nwdState net).
  
  Lemma reachable_revert_step :
    forall st st' out,
      reachable step_async_disk step_async_disk_init st ->
      step_async_disk st st' out ->
      (exists out, step_async (revertDiskNetwork st) (revertDiskNetwork st') out).
  Proof using.
    intros.
    unfold reachable in *.
    break_exists.
    match goal with H : step_async_disk _ _ _ |- _ => invcs H end.
    - admit.
    - admit.
  Admitted.
  
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
      econstructor;
        eauto using refl_trans_1n_n1_trace.
  Qed.

  Theorem true_in_reachable_disk_transform :
    forall P,
      true_in_reachable step_async step_async_init P ->
      true_in_reachable step_async_disk step_async_disk_init (fun net => P (revertDiskNetwork net)).
  Proof.
    intros.
    intros. find_apply_lem_hyp true_in_reachable_elim. intuition.
    apply true_in_reachable_reqs; eauto.
    intros. find_copy_apply_lem_hyp reachable_revert.
    find_apply_lem_hyp reachable_revert_step; auto.
    intuition.
    break_exists.
    eauto.
  Qed.
End DiskCorrect.
