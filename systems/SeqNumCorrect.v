Require Import Verdi.

Require Import FunctionalExtensionality.

Require Import SeqNum.

Section SeqNumCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.

  Lemma processPackets_correct :
    forall n l n' l',
      processPackets n l = (n', l') ->
      forall p,
        In p l' ->
        n' > (tmNum (snd p)).
  Proof.
    induction l; intros; simpl in *.
    - find_inversion. simpl in *. intuition.
    - break_match. find_inversion. simpl in *. intuition.
      + subst. simpl. omega.
      + eauto using le_gt_trans, le_plus_l.
  Qed.

  Lemma processPackets_num_monotonic :
    forall n l n' l',
      processPackets n l = (n', l') ->
      n' >= n.
  Proof.
    induction l; intros; simpl in *.
    - intros. find_inversion. intuition.
    - break_match. find_inversion.
      find_insterU. find_insterU. conclude_using eauto.
      omega.
  Qed.

  Lemma processPackets_ge_start :
    forall n l n' l',
      processPackets n l = (n', l') ->
      forall p,
        In p l' ->
        n <= (tmNum (snd p)).
  Proof.
    induction l; intros; simpl in *.
    - invcs H. intuition.
    - break_match.
      invcs H. intuition.
      + subst. simpl.
        apply processPackets_num_monotonic in Heqp0. intuition.
      + specialize (IHl n0 l0). apply IHl; auto.
  Qed.

  Lemma processPackets_nums_unique :
    forall n l n' l' p p',
      processPackets n l = (n', l') ->
      In p l' ->
      In p' l' ->
      p <> p' ->
      (tmNum (snd p)) <> (tmNum (snd p')).
  Proof.
    induction l; intros; simpl in *.
    - invcs H. intuition.
    - break_match. invcs H.
      intuition.
      + subst. intuition.
      + subst. simpl in *.
        apply processPackets_correct with (p := p') in Heqp0; intuition.
      + subst. simpl in *.
        apply processPackets_correct with (p := p) in Heqp0; intuition.
      + apply IHl with n0 l0 p p'; intuition.
  Qed.

  
  Lemma processPackets_seq_eq :
    forall n l n' l' x y,
      processPackets n l = (n', l') ->
      In x l' ->
      In y l' ->
      tmNum (snd x) = tmNum (snd y) ->
      x = y.
  Proof.
    induction l; intros; simpl in *.
    - find_inversion. simpl in *. intuition.
    - break_match. find_inversion. simpl in *.
      intuition; subst; simpl in *; eauto;
      subst; eapply processPackets_correct in Heqp; eauto; omega.
  Qed.


  Lemma processPackets_NoDup : forall n l n' l',
                                  processPackets n l = (n', l') ->
                                  NoDup l'.
  Proof.
    induction l; intros.
    - simpl in *. find_inversion. constructor.
    - simpl in *. break_match. find_inversion.
      specialize (IHl n0 l0). concludes.
      constructor; auto.
      intro.

      eapply processPackets_correct in H; eauto.
      simpl in *. omega.
  Qed.

  Lemma processPackets_preserves_messages :
    forall n l,
      map (fun p => (fst p, tmMsg (snd p))) (snd (processPackets n l)) = l.
  Proof.
    induction l.
    - auto.
    - simpl. break_match. simpl in *. rewrite IHl. destruct a. auto.
  Qed.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.
  Definition seq_num_packet := @packet _ multi_params.
  Definition seq_num_network := @network _ multi_params.
  
  Definition revertPacket (p : seq_num_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (pSrc p) (pDst p) (tmMsg (pBody p)).

  Definition pkt_eq_dec (x y : seq_num_packet) : {x = y} + {x <> y}.
    repeat decide equality.
    apply msg_eq_dec.
    apply name_eq_dec.
    apply name_eq_dec.
  Defined.

  Definition revertNetwork (net: seq_num_network) : orig_network :=
    mkNetwork
      (map revertPacket
           (filter (fun (p : seq_num_packet) =>
                      if member (tmNum (pBody p)) (tdSeen (nwState net (pDst p))
                                                          (pSrc p))
                      then false else true)
                   (dedup pkt_eq_dec
                          (nwPackets net))))
      (fun h => (tdData (nwState net h))).

  Lemma network_eq (net net' : orig_network) :
    nwState net = nwState net' ->
    nwPackets net = nwPackets net' ->
    net = net'.
  Proof.
    intros; destruct net, net'.
    simpl in *.
    subst.
    auto.
  Qed.

  Definition sequence_sane (net : seq_num_network) :=
    (forall p,
       In p (nwPackets net) ->
       tmNum (pBody p) < (tdNum ((nwState net) (pSrc p)))).

  Lemma reachable_sane :
    true_in_reachable step_dup step_async_init sequence_sane.
  Proof.
    apply inductive_invariant_true_in_reachable. unfold inductive_invariant, inductive.
    unfold sequence_sane. simpl in *. intuition.
    match goal with
      | [ H : step_dup _ _ _ |- _ ] =>
        invcs H
    end; try find_inversion.
    - (* deliver case *)
      unfold seq_num_net_handlers in *.
      simpl in *.
      do_in_app. intuition.
      + (* p is a new packet *)
        do_in_map.
        subst; simpl in *.
        repeat break_match; try find_inversion; simpl in *; intuition.
        eapply processPackets_correct; eauto.
      + (* p is an old packet *)
        simpl in *.
        repeat find_rewrite.
        do_in_app.
        repeat break_match; try find_inversion.
        * rewrite <- e. intuition.
        * apply processPackets_num_monotonic in Heqp0.
          apply lt_le_trans with (m := (tdNum (nwState a (pDst p0)))); auto.
          rewrite <- e. intuition.
        * intuition.
        * intuition.
    - unfold seq_num_input_handlers in *. simpl in *. do_in_app. intuition.
      + do_in_map. subst; simpl in *.
        repeat break_match; try find_inversion; simpl in *; intuition.
        eapply processPackets_correct; eauto.
      + simpl in *. 
        repeat break_match; try find_inversion;
        simpl in *; find_apply_lem_hyp processPackets_num_monotonic;
        find_apply_hyp_hyp; try omega.
    - in_crush; eauto with *.
  Qed.

  Definition sequence_seen (net : seq_num_network) :=
    forall h h' n,
      In n (tdSeen (nwState net h') h) ->
      n < (tdNum (nwState net h)).

  Lemma reachable_seen :
    true_in_reachable step_dup step_async_init sequence_seen.
  Proof.
    apply true_in_reachable_reqs; 
    unfold sequence_seen; simpl in *; intuition.
    find_apply_lem_hyp reachable_sane.
    unfold sequence_sane in *.
    match goal with H : step_dup _ _ _ |- _ => invcs H end.
    - (* step case *)
      unfold seq_num_net_handlers in *.
      repeat (break_match; try find_inversion; simpl in *; eauto);
      match goal with
        | [ H : processPackets _ _ = _ |- _ ] =>
          apply processPackets_num_monotonic in H
      end;
      try break_if; simpl in *; intuition; subst; eauto;
      repeat find_rewrite; (eapply lt_le_trans; [|eauto]; eauto).
    - unfold seq_num_input_handlers in *.
      repeat (break_match; try find_inversion; simpl in *; eauto);
      match goal with
        | [ H : processPackets _ _ = _ |- _ ] =>
          apply processPackets_num_monotonic in H
      end;
      try break_if; simpl in *; intuition; subst; eauto;
      repeat find_rewrite;
      (eapply lt_le_trans; [|eauto]; eauto).
    - eauto.
  Qed.

  Definition sequence_equality (net : seq_num_network) :=
    forall p p',
      In p (nwPackets net) ->
      In p' (nwPackets net) ->
      (tmNum (pBody p)) = (tmNum (pBody p')) ->
      pSrc p = pSrc p' ->
      p = p'.

  Theorem reachable_equality :
    true_in_reachable step_dup step_async_init sequence_equality.
  Proof.
    apply true_in_reachable_reqs; 
    unfold sequence_equality; simpl in *; intuition.
    match goal with
        H : reachable _ _ _ |- _ =>
        apply reachable_sane in H
    end.
    unfold sequence_sane, sequence_equality in *.
    intros.
    match goal with H : step_dup _ _ _ |- _ => invcs H end; simpl in *; find_inversion.
    - unfold seq_num_net_handlers in *.
      repeat do_in_app.
      repeat find_rewrite.
      repeat break_match; find_inversion; simpl in *; intuition;
      repeat do_in_map; subst; simpl in *.
      + repeat do_in_app. intuition.
      + find_inversion.
        match goal with
          | x : prod _ _, x' : prod _ _ |- _ =>
            replace x with x' by (eapply processPackets_seq_eq; eauto)
        end; auto.
      + match goal with H : processPackets _ _ = _ |- _ =>
                        eapply processPackets_ge_start in H
        end; eauto.
        match goal with
            _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ =>
            specialize (H p); forward H; [in_crush|]; [concludes]
        end. simpl in *. repeat find_rewrite. omega.
      + find_inversion.
        match goal with H : processPackets _ _ = _ |- _ =>
                        eapply processPackets_ge_start in H
        end; eauto.
        match goal with
            _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ =>
            specialize (H p); forward H; [in_crush|]; [concludes]
        end. simpl in *. repeat find_rewrite. omega.
      + match goal with
            H : forall _ _ : packet, In _ _ -> _ |- ?p = ?p' =>
            specialize (H p p'); repeat (forward H; [in_crush|]; concludes)
        end; auto.
    - unfold seq_num_input_handlers in *.
      repeat do_in_app.
      repeat break_match; find_inversion; simpl in *; intuition;
      repeat do_in_map; subst; simpl in *.
      + find_inversion.
        match goal with
          | x : prod _ _, x' : prod _ _ |- _ =>
            replace x with x' by (eapply processPackets_seq_eq; eauto)
        end; auto.
      + match goal with H : processPackets _ _ = _ |- _ =>
                        eapply processPackets_ge_start in H
        end; eauto.
        match goal with
            _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ =>
            specialize (H p); forward H; [in_crush|]; [concludes]
        end. simpl in *. repeat find_rewrite. omega.
      + find_inversion.
        match goal with H : processPackets _ _ = _ |- _ =>
                        eapply processPackets_ge_start in H
        end; eauto.
        match goal with
            _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ =>
            specialize (H p); forward H; [in_crush|]; [concludes]
        end. simpl in *. repeat find_rewrite. omega.
    - repeat find_rewrite. in_crush.
  Qed.

  Lemma revertNetwork_In :
    forall net (p : seq_num_packet),
      In p (nwPackets net) ->
      ~ In (tmNum (pBody p)) (tdSeen (nwState net (pDst p)) (pSrc p)) ->
      In (revertPacket p) (nwPackets (revertNetwork net)).
  Proof.
    intros. unfold revertNetwork. simpl in *.
    in_crush.
    apply filter_In. intuition.
    - apply dedup_In. auto.
    - break_if; intuition.
  Qed.

  Lemma revertNetwork_packets :
    forall xs net (p : seq_num_packet) ys,
      ~ In (tmNum (pBody p)) (tdSeen (nwState net (pDst p)) (pSrc p)) ->
      nwPackets net = xs ++ p :: ys ->
      exists xs' ys',
        nwPackets (revertNetwork net) =
        xs' ++ (revertPacket p) :: ys'.
  Proof.
    intros.
    apply in_split. apply revertNetwork_In; repeat find_rewrite; in_crush.
  Qed.

  Lemma processPackets_dedup :
    forall processed (rest : list seq_num_packet) n' l h net,
      (forall p, In p rest -> In p (nwPackets net)) ->
      sequence_sane net ->
      processPackets (tdNum (nwState net h)) l = (n', processed) ->
      dedup pkt_eq_dec ((@send_packets _ multi_params h processed) ++ rest)
      = (send_packets h processed) ++ (dedup pkt_eq_dec rest).
  Proof.
    intros. simpl in *.
    rewrite dedup_app; f_equal.
    - apply dedup_NoDup_id.
      apply NoDup_map_injective; eauto using processPackets_NoDup.
      intros. find_inversion.
      rewrite surjective_pairing at 1.
      rewrite surjective_pairing.
      unfold msg in *. simpl in *.
      repeat find_rewrite. auto.
    - intuition.
      subst.
      find_apply_lem_hyp in_map_iff. break_exists. intuition.
      find_eapply_lem_hyp processPackets_ge_start; eauto.
      match goal with
        | _ : In ?p _, net : network |- _ =>
          assert (In p (nwPackets net)) by eauto
      end.
      unfold sequence_sane in *.
      find_apply_hyp_hyp. simpl in *. subst. simpl in *. omega.
  Qed.

  Lemma revertNetwork_deliver_step :
    forall (st : seq_num_network) p xs ys (d : @data orig_base_params) l l' n,
      sequence_sane st ->
      sequence_seen st ->
      sequence_equality st ->
      nwPackets st = xs ++ p :: ys ->
      ~ In (tmNum (pBody p)) (tdSeen (nwState st (pDst p)) (pSrc p)) ->
      processPackets (tdNum (nwState st (pDst p))) l = (n, l') ->
      exists xs' ys',
        nwPackets (revertNetwork st) = xs' ++ revertPacket p :: ys' /\
        revertNetwork
          (@mkNetwork _ multi_params
                      (map
                         (fun m : name * seq_num_msg =>
                            {| pSrc := pDst p; pDst := fst m; pBody := snd m |})
                         l' ++ xs ++ ys)
                      (update name_eq_dec (nwState st) (pDst p)
                              (@mkseq_num_data _ orig_multi_params
                                               n
                                               (fun nm : name =>
                                                  if name_eq_dec nm (pSrc p)
                                                  then
                                                    tmNum (pBody p)
                                                          :: tdSeen (nwState st (pDst p)) (pSrc p)
                                                  else tdSeen (nwState st (pDst p)) nm)
                                               d)))
        = {|
          nwPackets := (@send_packets _ orig_multi_params (pDst p) l) ++ xs' ++ ys';
          nwState := update name_eq_dec (nwState (revertNetwork st)) (pDst p) d
        |}.
  Proof.
    intros.
    simpl in *.
    unfold revertNetwork.
    simpl in *.
    repeat find_rewrite.
    match goal with
        [ |- context [ dedup ?eq (map ?f ?l ++ ?xs ++ ?ys) ] ] =>
        assert (dedup eq (map f l ++ xs ++ ys) = (map f l) ++ (dedup eq (xs ++ ys)))
          by (find_eapply_lem_hyp processPackets_dedup;
              eauto; repeat find_rewrite; in_crush)
    end.
    find_rewrite.
    rewrite filter_app.
    rewrite map_app.
    assert (In p (nwPackets st)) by (find_rewrite; in_crush).
    match goal with
      | H : In _ _ |- _ =>
        apply dedup_In with (A_eq_dec := pkt_eq_dec) in H
    end.
    find_apply_lem_hyp in_split. break_exists. repeat find_rewrite.
    find_copy_apply_lem_hyp dedup_partition.
    unfold seq_num_packet in *.
    repeat find_rewrite.
    assert (NoDup (x ++ p :: x0)) by (repeat find_reverse_rewrite; apply NoDup_dedup).
    match goal with
      | [ |- context [ filter ?f (?xs ++ ?p :: ?ys) ] ] =>
        assert (In p (filter f (xs ++ p :: ys)))
          by (apply filter_In; repeat break_if; intuition)
    end. find_apply_lem_hyp in_split. break_exists.
    repeat find_rewrite.
    exists (map revertPacket x1), (map revertPacket x2).
    intuition; map_crush; auto.
    simpl in *.
    f_equal. f_equal.
    - rewrite filter_true_id.
      + match goal with
          | _ : processPackets ?n ?l = _ |- _ =>
            rewrite <- (processPackets_preserves_messages n l)
        end.
        find_rewrite. simpl in *.
        unfold revertPacket.
        repeat rewrite map_map. auto.
      + intros.
        in_crush.
        find_eapply_lem_hyp processPackets_ge_start; [|eauto].
        match goal with
            p : packet |- _ =>
            assert (tmNum (pBody p) < tdNum (nwState st (pSrc p))) by
                (eapply_prop sequence_sane; find_rewrite; in_crush)
        end.
        repeat (break_if; simpl in *; repeat find_rewrite; intuition);
          unfold sequence_seen in *; find_apply_hyp_hyp; omega.
    - rewrite <- filter_except_one
      with (f := (fun p0 : seq_num_packet =>
                    if member (tmNum (pBody p0)) (tdSeen (nwState st (pDst p0)) (pSrc p0))
                    then false
                    else true)) (x := p) (A_eq_dec := pkt_eq_dec).
      + unfold seq_num_packet in *. repeat find_rewrite.
        rewrite filter_app.
        find_apply_lem_hyp filter_partition; intuition.
        repeat find_rewrite. eauto using map_app.
      + intros. repeat (break_if; simpl in *; repeat find_rewrite; intuition).
        exfalso.
        match goal with H : _ = _ -> False |- _ => apply H end.
        eapply_prop sequence_equality; repeat find_rewrite; in_crush.
        find_apply_lem_hyp in_dedup_was_in. in_crush.
      + repeat (break_if; simpl in *; intuition).
    - apply functional_extensionality. intros; repeat break_if; simpl in *; intuition.
  Qed.

  Theorem revertNetwork_input :
    forall (st : seq_num_network) h (d : @data orig_base_params) l l' n,
      sequence_sane st ->
      sequence_seen st ->
      sequence_equality st ->
      processPackets (tdNum (nwState st h)) l = (n, l') ->
      revertNetwork
        (@mkNetwork _ multi_params
                    (send_packets h l' ++ nwPackets st)
                    (update name_eq_dec (nwState st) h
                            (@mkseq_num_data _ orig_multi_params
                                             n
                                             (tdSeen (nwState st h))
                                             d)))
        = {|
          nwPackets := (@send_packets _ orig_multi_params h l) ++ (nwPackets (revertNetwork st));
          nwState := update name_eq_dec (nwState (revertNetwork st)) h d
        |}.
  Proof.
    intros.
    unfold revertNetwork.
    simpl in *.
    match goal with
        [ |- context [ dedup ?eq (map ?f ?l ++ ?l') ] ] =>
        assert (dedup eq (map f l ++ l') = (map f l) ++ (dedup eq l'))
          by (find_eapply_lem_hyp processPackets_dedup;
              eauto; repeat find_rewrite; in_crush)
    end.
    find_rewrite.
    rewrite filter_app. rewrite map_app. f_equal. f_equal.
    - rewrite filter_true_id.
      + match goal with
          | _ : processPackets ?n ?l = _ |- _ =>
            rewrite <- (processPackets_preserves_messages n l)
        end.
        find_rewrite. simpl in *.
        unfold revertPacket.
        repeat rewrite map_map. auto.
      + intros.
        in_crush.
        find_eapply_lem_hyp processPackets_ge_start; [|eauto].
        repeat (break_if; simpl in *; repeat find_rewrite; intuition);
          unfold sequence_seen in *; find_apply_hyp_hyp; omega.
    - f_equal. apply filter_fun_ext_eq.
      intros. repeat (break_if; simpl in *; repeat find_rewrite; intuition).
    - apply functional_extensionality. intros; repeat break_if; simpl in *; intuition.
  Qed.

  (* We need this for dedup_eliminates_duplicates *)
  Arguments dedup _ _ _ : simpl nomatch.
  
  Lemma reachable_revert_step :
    forall st st' out,
      reachable step_dup step_async_init st ->
      step_dup st st' out ->
      (exists out, step_async (revertNetwork st) (revertNetwork st') out)
      \/ revertNetwork st = revertNetwork st'.
  Proof.
    intros.
    find_copy_apply_lem_hyp reachable_sane.
    find_copy_apply_lem_hyp reachable_seen.
    find_copy_apply_lem_hyp reachable_equality.
    break_exists.
    match goal with H : step_dup _ _ _ |- _ => invcs H end.
    - unfold seq_num_net_handlers in *. break_if.
      + right. find_inversion. simpl in *.
        unfold revertNetwork. simpl in *. intuition.
        f_equal.
        * f_equal. find_rewrite. symmetry.
          match goal with
            | |- filter ?f _ = filter ?g _ =>
              assert (f = g) by
                  (apply functional_extensionality;
                   intros; repeat break_if; repeat find_rewrite; intuition)
          end.
          find_rewrite.
          apply filter_dedup.
          break_if; intuition.
        * apply functional_extensionality.
          intros. break_if; subst; intuition.
      + left. repeat break_let. find_inversion.
        eexists.
        find_eapply_lem_hyp revertNetwork_deliver_step; eauto.
        break_exists.
        intuition.
        econstructor; eauto.
    - left. unfold seq_num_input_handlers in *. repeat break_let.
      find_inversion.
      eexists. find_eapply_lem_hyp revertNetwork_input; eauto.
      econstructor 2; simpl; eauto.
    - right.
      unfold revertNetwork.
      f_equal. f_equal. f_equal.
      simpl. find_rewrite. eauto using dedup_eliminates_duplicates.
  Qed.

  Theorem reachable_revert :
    true_in_reachable step_dup step_async_init
                      (fun st =>
                         reachable step_async step_async_init (revertNetwork st)).
  Proof.
    apply true_in_reachable_reqs.
    - unfold revertNetwork. simpl.
      unfold reachable. exists []. constructor.
    - intros.
      find_apply_lem_hyp reachable_revert_step; auto.
      intuition.
      + unfold reachable in *.
        break_exists.
        eexists.
        apply refl_trans_n1_1n_trace.
        econstructor; eauto using refl_trans_1n_n1_trace.
      + find_rewrite. auto.
  Qed.

  Theorem true_in_reachable_transform :
    forall P,
      true_in_reachable step_async step_async_init P ->
      true_in_reachable step_dup step_async_init (fun net => P (revertNetwork net)).
  Proof.
    intros. find_apply_lem_hyp true_in_reachable_elim. intuition.
    apply true_in_reachable_reqs; eauto.
    intros. find_copy_apply_lem_hyp reachable_revert.
    find_apply_lem_hyp reachable_revert_step; auto.
    intuition.
    - break_exists. eauto.
    - repeat find_rewrite. auto.
  Qed.

End SeqNumCorrect.
