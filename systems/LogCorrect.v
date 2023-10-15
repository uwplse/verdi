Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.

Require Import Verdi.Log.
Require Import FunctionalExtensionality.

Section LogCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.

  Context {data_serializer : Serializer data}.
  Context {name_serializer : Serializer name}.
  Context {msg_serializer : Serializer msg}.
  Context {input_serializer : Serializer input}.

  Variable snapshot_interval : nat.

  Instance log_base_params : BaseParams := @log_base_params orig_base_params.
  Instance log_multi_params : DiskOpMultiParams log_base_params := log_multi_params snapshot_interval.
  Instance log_failure_params : DiskOpFailureParams log_multi_params := log_failure_params snapshot_interval.

  Lemma apply_log_app : forall h d entries e,
      apply_log h d (entries ++ [e]) =
      apply_entry h (apply_log h d entries) e.
  Proof using.
    intros.
    unfold apply_log.
    rewrite fold_left_app.
    reflexivity.
  Qed.

  Definition disk_correct dsk h st  :=
    exists s (entries : list entry) (snap : data),
      dsk Count = Some (serialize (length entries)) /\
      dsk Log = Some s /\
      IOStreamWriter.unwrap s = IOStreamWriter.unwrap (list_serialize_rec entry _ entries) /\
      dsk Snapshot = Some (serialize snap) /\
      log_num_entries st = length entries /\
      (apply_log h snap entries = log_data st).

  Lemma log_net_handlers_spec :
    forall dst src m st ops out st' l dsk dsk',
      disk_correct dsk dst st ->
      log_net_handlers snapshot_interval dst src m st = (ops, out, st', l) ->
      apply_ops dsk ops = dsk' ->
      disk_correct dsk' dst st'.
  Proof using.
    intros.
    unfold disk_correct in *.
    unfold log_net_handlers, log_handler_result in *;
      break_if; do 2 break_let.
    - find_inversion.
      simpl.
      exists IOStreamWriter.empty, [], d.
      intuition.
    - find_inversion.
      simpl.
      break_exists.
      intuition.
      match goal with
      | _ : dsk Log = Some ?s, _ : apply_log _ ?d ?entries = _ |- _ =>
        exists (s +$+ (serialize (inr (src, m) : entry))), (entries ++ [inr (src, m)]), d
      end.
      intuition.
      + match goal with
          | H : context [log_num_entries] |- _ => rewrite H
          end.
          rewrite app_length.
          simpl.
          rewrite Nat.add_1_r.
          reflexivity.
      + break_match.
        * find_inversion.
          reflexivity.
        * congruence.
      + cheerios_crush.
        rewrite serialize_snoc.
        match goal with
        | H : IOStreamWriter.unwrap _ = IOStreamWriter.unwrap _ |- _ => rewrite H
        end.
        reflexivity.
      + match goal with
        | H : context [log_num_entries] |- _ => rewrite H
        end.
        rewrite app_length.
        simpl.
        rewrite Nat.add_1_r.
        reflexivity.
      + rewrite apply_log_app.
        match goal with
          | H : context [apply_log] |- _ => rewrite H
        end.
        simpl.
        match goal with
        | H : context [net_handlers] |- _ => rewrite H
        end.
        reflexivity.
  Qed.

  Lemma log_input_handlers_spec :
    forall h m st ops out st' l dsk dsk',
      disk_correct dsk h st ->
      log_input_handlers snapshot_interval h m st = (ops, out, st', l) ->
      apply_ops dsk ops = dsk' ->
      disk_correct dsk' h st'.
  Proof using.
    intros.
    unfold disk_correct in *.
    unfold log_input_handlers, log_handler_result in *;
      break_if; do 2 break_let.
    - find_inversion.
      simpl.
      exists IOStreamWriter.empty, [], d.
      intuition.
    - find_inversion.
      simpl.
      break_exists.
      intuition.
      match goal with
      | _ : dsk Log = Some ?s, _ : apply_log _ ?d ?entries = _ |- _ =>
        exists (s +$+ (serialize (inl m : entry))), (entries ++ [inl m]), d
      end.
      intuition.
      + match goal with
          | H : context [log_num_entries] |- _ => rewrite H
          end.
          rewrite app_length.
          simpl.
          rewrite Nat.add_1_r.
          reflexivity.
      + break_match.
        * find_inversion.
          reflexivity.
        * congruence.
      + cheerios_crush.
        rewrite serialize_snoc.
        match goal with
        | H : IOStreamWriter.unwrap _ = IOStreamWriter.unwrap _ |- _ => rewrite H
        end.
        reflexivity.
      + match goal with
        | H : context [log_num_entries] |- _ => rewrite H
        end.
        rewrite app_length.
        simpl.
        rewrite Nat.add_1_r.
        reflexivity.
      + rewrite apply_log_app.
        match goal with
          | H : context [apply_log] |- _ => rewrite H
        end.
        simpl.
        match goal with
        | H : context [input_handlers] |- _ => rewrite H
        end.
        reflexivity.
  Qed.

  Lemma disk_correct_reboot : forall net h d ops,
      disk_correct (nwdoDisk net h) h (nwdoState net h) ->
      do_log_reboot snapshot_interval h (disk_to_channel (nwdoDisk net h)) = (d, ops) ->
      disk_correct (apply_ops (nwdoDisk net h) ops) h d.
  Proof using.
    intros net h d dsk H_correct H_reboot.
    unfold do_log_reboot, disk_to_channel, channel_to_log, from_channel in *.
    unfold disk_correct in *. break_exists. intuition.
    repeat find_rewrite.
    repeat rewrite IOStreamWriter.channel_wrap_unwrap in *.
    repeat rewrite serialize_deserialize_id_nil in H_reboot.
    rewrite <- (app_nil_r (IOStreamWriter.unwrap _)) in H_reboot.
    repeat find_rewrite.
    rewrite list_serialize_deserialize_id_rec in H_reboot.
    find_inversion.
    exists (IOStreamWriter.empty).
    exists [].
    exists (reboot (apply_log h x1 x0)).
    intuition.
  Qed.

  Lemma disk_correct_invariant : forall net failed tr,
      @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr ->
      forall h, disk_correct (nwdoDisk net h) h (nwdoState net h).
  Proof using.
    intros net failed tr H_st h.
    remember step_failure_disk_ops_init as x.
    change net with (snd (failed, net)).
    induction H_st using refl_trans_1n_trace_n1_ind.
    - subst.
      intros.
      simpl in *.
      unfold disk_correct.
      simpl.
      exists IOStreamWriter.empty, [], (init_handlers h).
      intuition.
    - concludes.
      match goal with H : step_failure_disk_ops _ _ _ |- _ => invcs H end.
      + break_if.
        * rewrite e in *.
          intuition.
            match goal with
          | [G : disk_correct _ _ _, H : log_net_handlers _ _ _ _ _ = _ |- _] =>
            apply (log_net_handlers_spec _ _ _ _ _ _ _ _ _ _  G H)
          end.
          reflexivity.
        * assumption.
      + break_if.
        * rewrite e in *.
          match goal with
          | [G : disk_correct _ _ _, H : log_input_handlers _ _ _ _ = _ |- _] =>
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
      @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr ->
      forall h d dsk, do_reboot h (disk_to_channel (nwdoDisk net h)) = (d, dsk) ->
                 log_data d = reboot (log_data (nwdoState net h)).
  Proof using.
    intros net failed tr H_st h d dsk H_reboot.
    apply disk_correct_invariant with (h := h) in H_st.
    unfold disk_correct in *.
    break_exists. intuition.
    simpl in *.
    unfold do_log_reboot, channel_to_log, disk_to_channel in *. find_inversion.
    simpl.
    repeat match goal with
           | H : nwdoDisk net h _ = Some _ |- _ => rewrite H
           end.
    unfold from_channel.
    repeat rewrite IOStreamWriter.channel_wrap_unwrap in *.
    rewrite serialize_deserialize_id_nil.
    rewrite <- (app_nil_r (IOStreamWriter.unwrap _)).
    match goal with
    | H : IOStreamWriter.unwrap _ = IOStreamWriter.unwrap _ |- _ => rewrite H
    end.
    rewrite nat_serialize_deserialize_id.
    rewrite <- (app_nil_r (IOStreamWriter.unwrap _)).
    rewrite list_serialize_deserialize_id_rec.
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
    mkNetwork (map revertPacket (nwdoPackets net)) (fun h => (log_data (nwdoState net h))).

  Theorem log_step_failure_step :
    forall net net' failed failed' tr tr',
      @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr ->
      @step_failure_disk_ops _ _ log_failure_params (failed, net) (failed', net') tr' ->
      step_failure (failed, revertLogNetwork net) (failed', revertLogNetwork net') tr'.
  Proof using.
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
      apply @StepFailure_deliver with (xs := map revertPacket xs)
                                     (ys := map revertPacket ys)
                                     (d := log_data d)
                                     (l := l).
      + reflexivity.
      + assumption.
      + simpl.
        unfold log_net_handlers, log_handler_result in *.
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
      apply @StepFailure_input with (d := log_data d) (l := l).
      + assumption.
      + unfold log_input_handlers, log_handler_result in *.
        do 2 break_let.
        break_if;
          find_inversion;
          assumption.
      + rewrite apply_if.
        reflexivity.
    - unfold revertLogNetwork.
      simpl. find_rewrite.
      rewrite map_app. simpl.
      apply @StepFailure_drop with (xs := map revertPacket xs)
                                  (p := revertPacket p)
                                  (ys := map revertPacket ys).
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
    - apply @StepFailure_reboot with (h := h).
      + assumption.
      + reflexivity.
      + unfold revertLogNetwork. simpl.
        apply reboot_invariant with (h := h) (d := d) (dsk := ops) in H.
        * rewrite <- H.
          rewrite apply_if.
          reflexivity.
        * assumption.
  Qed.

  Lemma log_step_failure_star_simulation :
    forall net failed tr,
      step_failure_disk_ops_star step_failure_disk_ops_init (failed, net) tr ->
      step_failure_star step_failure_init (failed, revertLogNetwork net) tr.
  Proof using.
    intros net failed tr H_star.
    remember step_failure_disk_ops_init as y in *.
    change failed with (fst (failed, net)).
    change net with (snd (failed, net)) at 2.
    revert Heqy.
    induction H_star using refl_trans_1n_trace_n1_ind; intro H_init.
    - find_rewrite.
      simpl; unfold revertLogNetwork; simpl.
      unfold step_failure_init, step_async_init.
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
