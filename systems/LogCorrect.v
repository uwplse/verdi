Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.

Require Import Verdi.Log.

Section LogCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.

  Context {data_serializer : Serializer data}.
  Context {l_name_serializer : Serializer name}.
  Context {msg_serializer : Serializer msg}.
  Context {input_serializer : Serializer input}.

  Context {snapshot_interval : nat}.
  Hypothesis reboot_idem : forall d, reboot (reboot d) = reboot d.

  Lemma f :
    deserialize_top
             (list_deserialize_rec entry
                (sum_Serializer input (name * msg) input_serializer
                   (pair_Serializer name msg l_name_serializer msg_serializer)) 0)
             (serialize_top IOStreamWriter.empty) = Some [].
  Proof.
    unfold deserialize_top, serialize_top.
    simpl.
    cheerios_crush.
  Qed.

  Lemma disk_follows_local_state : forall net failed tr (h : name) d dsk,
      @step_failure_log_star _ _
                             (log_failure_params (snapshot_interval := snapshot_interval)) step_failure_log_init (failed, net) tr ->
      (do_reboot (snapshot_interval := snapshot_interval))
        h (disk_to_wire (nwdoDisk net h)) = (d, dsk) ->
      d = nwdoState net h.
  Proof.
    intros.
    remember step_failure_log_init as x.
    generalize dependent d. generalize dependent dsk.
    change net with (snd (failed, net)).
    induction H using refl_trans_1n_trace_n1_ind.
    - intros.
      rewrite Heqx in *.
      simpl in *.
      unfold disk_to_wire, init_disk, do_reboot in *.
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
      rewrite Heqx in *.
      admit.
  Admitted.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.

  Definition log_packet := @do_packet _ (log_multi_params (snapshot_interval := snapshot_interval)).
  Definition log_network := @do_network _ (log_multi_params (snapshot_interval := snapshot_interval)).


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
      Admitted.
End LogCorrect.
