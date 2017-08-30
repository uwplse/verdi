Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.

Require Import Verdi.Log.
Require Import FunctionalExtensionality.

Section LogCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {log_params : LogParams orig_multi_params}.

  Lemma apply_log_app : forall h d entries e,
      apply_log h d (entries ++ [e]) =
      apply_entry h (apply_log h d entries) e.
  Proof.
    intros.
    generalize dependent d.
    induction entries.
    - reflexivity.
    - intros.
      simpl.
      rewrite IHentries.
      reflexivity.
  Qed.

  Lemma serialize_snoc : forall {A} {sA : Serializer A} (a : A) l,
      IOStreamWriter.unwrap (list_serialize_rec _ _ l) ++
                            IOStreamWriter.unwrap (serialize a) =
      (IOStreamWriter.unwrap (list_serialize_rec _ _ (l ++ [a]))).
  Proof.
    intros.
    induction l;
      simpl;
      cheerios_crush.
    - rewrite app_nil_r.
      reflexivity.
    - rewrite <- IHl.
      reflexivity.
  Qed.
  Definition disk_correct dsk h st  :=
    exists entries snap,
      IOStreamWriter.unwrap (dsk Log) = IOStreamWriter.unwrap (list_serialize_rec entry _ entries) /\
      log_num_entries st = length entries /\
      ByteListReader.unwrap deserialize (IOStreamWriter.unwrap (dsk Count)) =
      Some (length entries, []) /\
      ByteListReader.unwrap deserialize (IOStreamWriter.unwrap (dsk Snapshot)) =
      Some (snap, []) /\
      (apply_log h snap entries = log_data st).

  Lemma log_net_handlers_spec :
    forall dst src m st
           ops out st' l
           dsk dsk',
      disk_correct dsk dst st ->
      log_net_handlers dst src m st = (ops, out, st', l) ->
      apply_ops dsk ops = dsk' ->
      disk_correct dsk' dst st'.
    intros.
    unfold disk_correct in *.
    break_exists.
    intuition.
    unfold log_net_handlers in *.
    break_if; do 2 break_let.
    - exists [], d.
      intuition.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        reflexivity.
      + find_inversion.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        rewrite serialize_deserialize_id_nil.
        reflexivity.
      + find_inversion.
        simpl.
        rewrite serialize_deserialize_id_nil.
        reflexivity.
      + find_inversion.
        reflexivity.
    - repeat break_and.
      exists (x ++ [inr (src, m)]), x0.
      intuition.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        cheerios_crush.
        match goal with
        | H : IOStreamWriter.unwrap (dsk Log) = _ |- _ => rewrite H
        end.
        rewrite serialize_snoc.
        reflexivity.
      + find_inversion.
        repeat find_rewrite.
        rewrite app_length.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        rewrite serialize_deserialize_id_nil.
        rewrite app_length.
        rewrite PeanoNat.Nat.add_1_r.
        repeat find_rewrite.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        assumption.
      + rewrite apply_log_app.
        match goal with
        | H : apply_log _ _ _ = _ |- _ => rewrite H
        end.
        find_inversion.
        simpl.
        match goal with
        | H : net_handlers _ _ _ _ = _ |- _ => rewrite H
        end.
        reflexivity.
  Qed.

  Lemma log_input_handlers_spec :
    forall dst m st
           ops out st' l
           dsk dsk',
      disk_correct dsk dst st ->
      log_input_handlers dst m st = (ops, out, st', l) ->
      apply_ops dsk ops = dsk' ->
      disk_correct dsk' dst st'.
    intros.
    unfold disk_correct in *.
    break_exists.
    intuition.
    unfold log_input_handlers in *.
    break_if; do 2 break_let.
    - exists [], d.
      intuition.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        reflexivity.
      + find_inversion.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        rewrite serialize_deserialize_id_nil.
        reflexivity.
      + find_inversion.
        simpl.
        rewrite serialize_deserialize_id_nil.
        reflexivity.
      + find_inversion.
        reflexivity.
    - repeat break_and.
      exists (x ++ [inl m]), x0.
      intuition.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        cheerios_crush.
        match goal with
        | H : IOStreamWriter.unwrap (dsk Log) = _ |- _ => rewrite H
        end.
        rewrite serialize_snoc.
        reflexivity.
      + find_inversion.
        repeat find_rewrite.
        rewrite app_length.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        rewrite serialize_deserialize_id_nil.
        rewrite app_length.
        rewrite PeanoNat.Nat.add_1_r.
        repeat find_rewrite.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        assumption.
      + rewrite apply_log_app.
        match goal with
        | H : apply_log _ _ _ = _ |- _ => rewrite H
        end.
        find_inversion.
        simpl.
        match goal with
        | H : input_handlers _ _ _ = _ |- _ => rewrite H
        end.
        reflexivity.
  Qed.

  Lemma disk_correct_reboot : forall net h d dsk,
      disk_correct (nwdoDisk net h) h (nwdoState net h) ->
      do_log_reboot h (disk_to_wire (nwdoDisk net h)) = (d, dsk) ->
      disk_correct dsk h d.
  Proof.
    intros net h d dsk H_correct H_reboot.
    unfold do_log_reboot, wire_to_log, disk_to_wire in *.
    unfold disk_correct in *. break_exists. intuition.
    unfold serialize_top, deserialize_top in *.
    repeat rewrite IOStreamWriter.wire_wrap_unwrap in *.
    repeat find_rewrite.
    rewrite <- (app_nil_r (IOStreamWriter.unwrap _)) in H_reboot.
    rewrite list_serialize_deserialize_id_rec' in H_reboot.
    find_inversion.
    exists [], (reboot (log_data (nwdoState net h))).
    intuition.
    - rewrite serialize_deserialize_id_nil.
      reflexivity.
    - rewrite serialize_deserialize_id_nil.
      find_rewrite.
      reflexivity.
    - find_rewrite.
      reflexivity.
  Qed.

  Lemma disk_correct_invariant : forall net failed tr,
      @step_failure_log_star _ _ log_failure_params step_failure_log_init (failed, net) tr ->
      forall h, disk_correct (nwdoDisk net h) h (nwdoState net h).
  Proof.
    intros net failed tr H_st h.
    remember step_failure_log_init as x.
    change net with (snd (failed, net)).
    induction H_st using refl_trans_1n_trace_n1_ind.
    - subst.
      intros.
      simpl in *.
      unfold disk_correct.
      exists [], (init_handlers h).
      intuition;
        simpl;
        rewrite serialize_deserialize_id_nil;
        reflexivity.
    - concludes.
      match goal with H : step_failure_log _ _ _ |- _ => invcs H end.
      + break_if.
        * rewrite e in *.
          match goal with
          | [G : disk_correct _ _ _, H : log_net_handlers _ _ _ _ = _ |- _] =>
            apply (log_net_handlers_spec _ _ _ _ _ _ _ _ _ _  G H)
          end.
          reflexivity.
        * assumption.
      + break_if.
        * rewrite e in *.
          match goal with
          | [G : disk_correct _ _ _, H : log_input_handlers _ _ _ = _ |- _] =>
            apply (log_input_handlers_spec  _ _ _ _ _ _ _ _ _ G H)
          end.
          reflexivity.
        * assumption.
      + assumption.
      + assumption.
      + assumption.
      + break_if.
        * repeat find_rewrite.
          find_apply_lem_hyp disk_correct_reboot;
            assumption.
        * assumption.
  Qed.

  Lemma reboot_invariant : forall net failed tr,
      @step_failure_log_star _ _ log_failure_params step_failure_log_init (failed, net) tr ->
      forall h d dsk, do_reboot h (disk_to_wire (nwdoDisk net h)) = (d, dsk) ->
                      log_data d = reboot (log_data (nwdoState net h)).
    intros net failed tr H_st h d dsk H_reboot.
    apply disk_correct_invariant with (h := h) in H_st.
    unfold disk_correct in *.
    break_exists. intuition.
    simpl in *.
    unfold do_log_reboot, wire_to_log, disk_to_wire in *.
    unfold deserialize_top, serialize_top in *.
    repeat rewrite IOStreamWriter.wire_wrap_unwrap in *.
    repeat find_rewrite.
    rewrite <- (app_nil_r (IOStreamWriter.unwrap _)) in H_reboot.
    rewrite list_serialize_deserialize_id_rec' in H_reboot.
    find_inversion.
    simpl.
    find_rewrite.
    reflexivity.
  Qed.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.

  Definition log_packet := @do_packet _ log_multi_params.
  Definition log_network := @do_network _ log_multi_params.

  Definition revertPacket (p : log_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (do_pSrc p) (do_pDst p) (do_pBody p).

  Definition revertLogNetwork (net: log_network) : orig_network :=
    mkNetwork (map revertPacket (nwdoPackets net))
              (fun h => (log_data (nwdoState net h))).

  Theorem log_step_failure_step :
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
    {
      induction l.
      * reflexivity.
      * intros.
        simpl.
        now rewrite IHl.
    }
    assert (apply_if : forall h d,
               (fun h0 : name => log_data (if name_eq_dec h0 h then d else nwdoState net h0)) =
               (fun h0 : name => if name_eq_dec h0 h
                                 then log_data d
                                 else log_data (nwdoState net h0))).
    {
      intros.
      extensionality h0.
      break_if; reflexivity.
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
      + simpl.
        rewrite apply_if.
        reflexivity.
    - unfold revertLogNetwork.
      simpl.
      repeat rewrite map_app.
      rewrite revert_send.
      apply StepFailure_input with (d0 := log_data d) (l0 := l).
      + assumption.
      + unfold log_input_handlers in *.
        do 2 break_let.
        break_if;
          find_inversion;
          assumption.
      + rewrite apply_if.
        reflexivity.
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
        apply reboot_invariant with (h := h) (d := d) (dsk := dsk) in H.
        * rewrite <- H.
          rewrite apply_if.
          reflexivity.
        * assumption.
  Qed.

  Lemma log_step_failure_star_simulation :
    forall net failed tr,
      step_failure_log_star step_failure_log_init (failed, net) tr ->
      step_failure_star step_failure_init (failed, revertLogNetwork net) tr.
  Proof.
    intros net failed tr H_star.
    remember step_failure_log_init as y in *.
    change failed with (fst (failed, net)).
    change net with (snd (failed, net)) at 2.
    revert Heqy.
    induction H_star using refl_trans_1n_trace_n1_ind; intro H_init.
    - find_rewrite.
      simpl; unfold revertLogNetwork; simpl.
      constructor.
    - concludes.
      destruct x' as (failed', net').
      destruct x'' as (failed'', net'').
      subst.
      apply RT1n_step with (y := (failed', revertLogNetwork net')).
      + apply IHH_star1.
      + eapply log_step_failure_step; eauto.
  Qed.
End LogCorrect.
