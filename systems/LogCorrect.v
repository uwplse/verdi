Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.

Require Import Verdi.Log.

Section LogCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {log_params : LogParams orig_multi_params}.

  Existing Instance log_data_serializer.
  Existing Instance log_name_serializer.
  Existing Instance log_msg_serializer.
  Existing Instance log_input_serializer.

  Lemma f :
    deserialize_top
             (list_deserialize_rec entry _ 0)
             (serialize_top IOStreamWriter.empty) = Some [].
  Proof.
    unfold deserialize_top, serialize_top.
    simpl.
    cheerios_crush.
  Qed.

  Lemma g : forall {A B} (f : A -> B) (c : bool) x y, f (if c then x else y) = if c then (f x) else (f y).
  Proof.
    intros.
    now break_if.
  Qed.

  Lemma disk_follows_local_state : forall net failed tr (h : name),
      @step_failure_log_star _ _ log_failure_params step_failure_log_init (failed, net) tr ->
      match do_reboot h (disk_to_wire (nwdoDisk net h)) with
      | (d, dsk) => d
      end = nwdoState net h.
  Proof.
    intros.
    remember step_failure_log_init as x.
    change net with (snd (failed, net)).
    induction H using refl_trans_1n_trace_n1_ind.
    - intros.
      rewrite Heqx in *.
      simpl in *.
      unfold disk_to_wire, init_disk, do_reboot, Log.do_reboot in *.
      break_let.
      break_match;
        unfold wire_to_log in *;
        repeat rewrite serialize_deserialize_top_id in Heqo;
        rewrite f in *.
      + break_let.
        break_let.
        find_inversion.
        find_inversion.
        reflexivity.
      + congruence.
    - concludes.
      break_let. break_let.
      rewrite Heqx in *.
      match goal with H : step_failure_log _ _ _ |- _ => invcs H end.
      + break_if.
        * admit.
        * match goal with H : do_reboot _ _ = _ |- _ => rewrite H in * end.
          find_inversion.
          reflexivity.
      + break_if.
        * admit.
        * match goal with H : do_reboot _ _ = _ |- _ => rewrite H in * end.
          find_inversion.
          reflexivity.
      + match goal with H : do_reboot _ _ = _ |- _ => rewrite H in * end.
        find_inversion.
        reflexivity.
      + match goal with H : do_reboot _ _ = _ |- _ => rewrite H in * end.
        find_inversion.
        reflexivity.
      + match goal with H : do_reboot _ _ = _ |- _ => rewrite H in * end.
        find_inversion.
        reflexivity.
      + break_if.
        * find_rewrite.
          admit.
        * match goal with H : do_reboot _ _ = _ |- _ => rewrite H in * end.
          find_inversion.
          reflexivity.
  Admitted.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.

  Definition log_packet := @do_packet _ log_multi_params.
  Definition log_network := @do_network _ log_multi_params.

  Definition revertPacket (p : log_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (do_pSrc p) (do_pDst p) (do_pBody p).

  Definition revertLogNetwork (net: log_network) : orig_network :=
    mkNetwork (map revertPacket (nwdoPackets net))
              (fun h => (log_data (nwdoState net h))).

  Theorem disk_step_failure_step :
    forall net net' failed failed' tr tr',
      @step_failure_log_star _ _ log_failure_params step_failure_log_init (failed, net) tr ->
      @step_failure_log _ _ log_failure_params (failed, net) (failed', net') tr' ->
      step_failure (failed, revertLogNetwork net)
                   (failed', revertLogNetwork net')
                   tr'.
  Proof.
    intros.
    assert (revert_packets : forall net, nwPackets (revertLogNetwork net) =
                        map revertPacket (nwdoPackets net)) by reflexivity.
    assert (revert_send : forall l h,
               map revertPacket (do_send_packets h l) = send_packets h l).
      { induction l.
        * reflexivity.
        * intros.
          simpl.
          now rewrite IHl.
      }
      invcs H0.
    - unfold revertLogNetwork.
      simpl.
      find_rewrite.
      repeat rewrite map_app. simpl.
      rewrite revert_send.
      assert (revert_packet : do_pDst p = pDst (revertPacket p)) by reflexivity.
      rewrite revert_packet in *.
      apply StepFailure_deliver with (xs0 := map revertPacket xs)
                                     (ys0 := map revertPacket ys)
                                     (d0 := log_data d)
                                     (l0 := l).
      + reflexivity.
      + assumption.
      + simpl.
        unfold log_net_handlers in *.
        break_let. break_let.
        break_if;
          find_inversion;
          rewrite revert_packet in *;
          assumption.
      + unfold log_data.
        break_let.
        simpl.
        admit.
    - unfold revertLogNetwork.
      simpl.
      repeat rewrite map_app.
      rewrite revert_send.
      admit.
    - unfold revertLogNetwork.
      simpl. find_rewrite.
      rewrite map_app. simpl.
      apply StepFailure_drop with (xs0 := map revertPacket xs)
                                  (p0 := revertPacket p)
                                  (ys0 := map revertPacket ys).
      + reflexivity.
      + rewrite map_app. reflexivity.
    - unfold revertLogNetwork.
      simpl. find_rewrite.
      rewrite map_app. simpl.
      apply (@StepFailure_dup _ _ _ _ _ _
                              (revertPacket p)
                              (map revertPacket xs)
                              (map revertPacket ys)).
      + reflexivity.
      + reflexivity.
    - constructor.
    - apply StepFailure_reboot with (h0 := h).
      + assumption.
      + reflexivity.
      + unfold revertLogNetwork. simpl.
        admit.
  Admitted.
End LogCorrect.
