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

  (* invariant: any of
     - all files absent
     - log and count present, snapshot absent
     - log, count, snapshot present
   *)

  Definition disk_correct dsk h st  :=
    exists entries snap,
      @channel_to_log _ _ _ _ _ _ snapshot_interval (disk_to_channel dsk) =
      Some (length entries, entries, snap) /\
      log_num_entries st = length entries /\
      (apply_log h snap entries = log_data st).

  Lemma disk_invariant : forall net failed tr,
      @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr ->
      forall h, ((forall f, nwdoDisk net h f = None) \/
                 (exists s1 s2, nwdoDisk net h Count = s1 /\
                                nwdoDisk net h Log = s2 /\
                                (nwdoDisk net h Snapshot = None \/
                                 exists s3, nwdoDisk net h Snapshot = Some s3))).
  Proof.
    intros net failed tr H_st.
    remember step_failure_disk_ops_init as x.
    change net with (snd (failed, net)).
    induction H_st using refl_trans_1n_trace_n1_ind.
    - left.
      intros.
      find_rewrite.
      simpl.
      unfold null_disk.
      reflexivity.
    - concludes.
      invcs H.
      + intros.
        admit.
      + admit.
      + intuition.
      + intuition.
      + intuition.
      + intuition.
        unfold do_log_reboot in *.
        do 2 break_let.
        find_inversion.
        simpl.
        specialize IHH_st1 with h0.
        intuition.
        * right.







  Lemma log_net_handlers_spec :
    forall dst src m st
           ops out st' l
           dsk dsk',
      disk_correct dsk dst st ->
      log_net_handlers snapshot_interval dst src m st = (ops, out, st', l) ->
      apply_ops dsk ops = dsk' ->
      disk_correct dsk' dst st'.
  Proof.
    intros.
    unfold disk_correct in *.
    unfold log_net_handlers in *;
      break_if; do 2 break_let.
    - find_inversion.
      simpl.
      unfold channel_to_log, disk_to_channel.
      simpl.
      unfold from_channel.
      repeat rewrite IOStreamWriter.channel_wrap_unwrap.
      rewrite serialize_deserialize_id_nil.
      simpl. cheerios_crush.
      rewrite serialize_deserialize_id_nil.
      exists [], d.
      intuition.
    - find_inversion.
      simpl.
      unfold channel_to_log, disk_to_channel.
      simpl.
      unfold from_channel.
      rewrite IOStreamWriter.channel_wrap_unwrap.
      break_exists.
      intuition.
      unfold channel_to_log, disk_to_channel in *.
      break_let.
      break_match.
      * break_match.





    intros.
    unfold disk_correct in *.
    intuition;
      unfold log_net_handlers in *;
      break_if; do 2 break_let;
        unfold channel_to_log, disk_to_channel, from_channel;
        repeat rewrite IOStreamWriter.channel_wrap_unwrap.
    - find_inversion.
      exists [], d.
      intuition.
      simpl.
      do 3 rewrite IOStreamWriter.channel_wrap_unwrap.
      rewrite serialize_deserialize_id_nil.
      rewrite <- (app_nil_r (IOStreamWriter.unwrap _)).
      assert (IOStreamWriter.empty = list_serialize_rec entry _ []) by reflexivity.
      rewrite H0.
      change 0 with (length (@nil entry)).
      rewrite list_serialize_deserialize_id_rec.
      rewrite serialize_deserialize_id_nil.
      reflexivity.
    - break_exists.
      find_inversion.
      unfold apply_ops.
      simpl.
      repeat rewrite IOStreamWriter.channel_wrap_unwrap.
      rewrite serialize_deserialize_id_nil.
      assert (IOStreamWriter.unwrap (serialize (inr (src, m) : entry)) =
              IOStreamWriter.unwrap (list_serialize_rec entry _ [(inr (src, m))]) ++ []).
      + simpl. cheerios_crush.
        repeat rewrite app_nil_r.
        reflexivity.
      +
        exists ([inr (src, m)]), (init_handlers dst).
        intuition.
        * match goal with
          | H : context[log_num_entries] |- _ => rewrite H
          end.
          change 1 with (length ([inr (src, m) : entry])).
          simpl.
          break_let.
          admit.
        *
  Admitted.

  Lemma log_input_handlers_spec :
    forall h m st
           ops out st' l
           dsk dsk',
      disk_correct dsk h st ->
      log_input_handlers snapshot_interval h m st = (ops, out, st', l) ->
      apply_ops dsk ops = dsk' ->
      disk_correct dsk' h st'.
  Proof.
    intros.
    unfold disk_correct in *.
    break_exists.
    intuition.
    unfold log_input_handlers in *.
    break_if; do 2 break_let.
    - exists IOStreamWriter.empty, [], d.
      intuition;
        try match goal with
            | H : _ = dsk' |- _ => rewrite <- H
            end;
        find_inversion;
        simpl;
        reflexivity.
    - repeat break_and.
      match goal with
      | _ : apply_log _ ?data ?entries = _,
            _ : dsk Log = Some ?s |- _ =>
        exists   (s +$+ serialize (inl m : entry)), (entries ++ [inl m : entry]), data
      end.
      intuition.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        cheerios_crush.
        repeat find_rewrite.
        rewrite app_length.
        rewrite NPeano.Nat.add_1_r.
        reflexivity.
      + find_inversion.
        simpl.
        repeat find_rewrite.
        reflexivity.
      + match goal with
        | H : _ = dsk' |- _ => rewrite <- H
        end.
        find_inversion.
        simpl.
        break_match.
        * find_inversion.
          reflexivity.
        * congruence.
      + find_inversion.
        rewrite IOStreamWriter.append_unwrap.
        match goal with
        | H : IOStreamWriter.unwrap _ = IOStreamWriter.unwrap _ |- _ => rewrite H
        end.
        rewrite serialize_snoc.
        reflexivity.
      + find_inversion.
        simpl.
        repeat find_rewrite.
        rewrite app_length.
        simpl.
        rewrite NPeano.Nat.add_1_r.
        reflexivity.
      + rewrite apply_log_app.
        find_inversion.
        unfold apply_entry.
        repeat find_reverse_rewrite.
        match goal with
        | H : input_handlers _ _ _ = _ |- _ => rewrite H
        end.
        reflexivity.
  Qed.

  Lemma disk_correct_reboot : forall net h d ops,
      disk_correct (nwdoDisk net h) h (nwdoState net h) ->
      do_log_reboot snapshot_interval
                    h
                    (disk_to_channel (nwdoDisk net h)) = (d, ops) ->
      disk_correct (apply_ops (nwdoDisk net h) ops) h d.
  Proof.
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
      forall h, (forall f, nwdoDisk net h f = None) \/
                disk_correct (nwdoDisk net h) h (nwdoState net h).
  Proof.
    intros net failed tr H_st h.
    remember step_failure_disk_ops_init as x.
    change net with (snd (failed, net)).
    induction H_st using refl_trans_1n_trace_n1_ind.
    - subst.
      intros.
      simpl in *.
      unfold disk_correct.
      left.
      reflexivity.
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
      @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr ->
      @step_failure_disk_ops _ _ log_failure_params (failed, net) (failed', net') tr' ->
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
      step_failure_disk_ops_star step_failure_disk_ops_init (failed, net) tr ->
      step_failure_star step_failure_init (failed, revertLogNetwork net) tr.
  Proof.
    intros net failed tr H_star.
    remember step_failure_disk_ops_init as y in *.
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
