Require Import Verdi.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Fixpoint distinct_pairs_and {A} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with
    | [] => True
    | x :: xs => (forall y, In y xs -> R x y) /\ distinct_pairs_and R xs
  end.

Class Decomposition (B : BaseParams) (M : MultiParams B) :=
  {
    state_invariant : (name -> data) -> Prop;
    network_invariant : (name -> data) -> packet -> Prop;
    network_network_invariant : packet -> packet -> Prop;

    network_network_invariant_sym :
      forall p1 p2,
        network_network_invariant p1 p2 ->
        network_network_invariant p2 p1 ;

    state_invariant_init : state_invariant init_handlers;

    state_invariant_maintained_input :
      forall h inp sigma st' out ps,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        state_invariant (update name_eq_dec sigma h st');
    state_invariant_maintained_deliver :
      forall p sigma st' out ps,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        state_invariant (update name_eq_dec sigma (pDst p) st');

    network_invariant_maintained_input_old :
      forall h inp sigma st' out ps p,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        network_invariant (update name_eq_dec sigma h st') p;
    network_invariant_maintained_input_new :
      forall h inp sigma st' out ps p,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        In (pDst p, pBody p) ps ->
        pSrc p = h ->
        network_invariant (update name_eq_dec sigma h st') p;

    network_invariant_maintained_deliver_old :
      forall sigma st' out ps p q,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        network_invariant sigma q ->
        network_network_invariant p q ->
        network_invariant (update name_eq_dec sigma (pDst p) st') q;
    network_invariant_maintained_deliver_new :
      forall sigma st' out ps p p',
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        In (pDst p', pBody p') ps ->
        pSrc p' = pDst p ->
        network_invariant (update name_eq_dec sigma (pDst p) st') p';

    network_network_invariant_maintained_input_old :
      forall h inp sigma st' out ps p p',
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        In (pDst p', pBody p') ps ->
        pSrc p' = h ->
        network_network_invariant p p';

    network_network_invariant_maintained_input_new :
      forall h inp sigma st' out ps,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        distinct_pairs_and network_network_invariant (map (fun m => mkPacket h (fst m) (snd m)) ps);

    network_network_invariant_maintained_deliver_old :
      forall sigma st' out ps p p' q,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        network_invariant sigma q ->
        network_network_invariant p q ->
        In (pDst p', pBody p') ps ->
        pSrc p' = pDst p ->
        network_network_invariant p' q;

    network_network_invariant_maintained_deliver_new :
      forall sigma st' out ps p,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        distinct_pairs_and network_network_invariant (map (fun m => mkPacket (pDst p) (fst m) (snd m)) ps)
  }.

Section Decomposition.
  Context `{d : Decomposition}.

  (* Fixpoint remove_one {A : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) a l :=
    match l with
      | x :: xs => if A_eq_dec a x then xs else x :: remove_one A_eq_dec a xs
      | [] => []
    end. *)

  Definition packet_eq_dec :
    forall p1 p2 : packet,
      {p1 = p2} + {p1 <> p2}.
  Proof.
    intros. decide equality; eauto using name_eq_dec,msg_eq_dec.
  Defined.


  Definition composed_invariant net :=
    (state_invariant (nwState net)) /\
    (forall p, In p (nwPackets net) -> network_invariant (nwState net) p) /\
    (distinct_pairs_and network_network_invariant (nwPackets net)).

  Lemma post_net_analyze_sent_packet :
    forall h p ms xs ys,
      In p (map (fun m => mkPacket h (fst m) (snd m)) ms ++ xs ++ ys) ->
      (In (pDst p, pBody p) ms /\ h = pSrc p) \/ In p (xs ++ ys).
  Proof.
    intros.
    in_crush. destruct x; simpl in *; eauto.
  Qed.

  Lemma post_input_analyze_sent_packet :
    forall h p ms l,
      In p (map (fun m => mkPacket h (fst m) (snd m)) ms ++ l) ->
      (In (pDst p, pBody p) ms /\ h = pSrc p) \/ In p l.
  Proof.
    intros.
    in_crush; destruct x; simpl in *; eauto.
  Qed.

  (* NB: generalizing this over R makes it useless to [eauto using]
     because the conclusion is too general. *)
  Lemma nw_nw_distinct_pairs_and_elim :
    forall xs a b ys l,
      l = xs ++ a :: ys ->
      In b (xs ++ ys) ->
      distinct_pairs_and network_network_invariant l ->
      network_network_invariant a b.
  Proof.
    induction xs; intros; subst; simpl in *; intuition eauto; subst; eauto.
    apply network_network_invariant_sym. eauto.
  Qed.

  Lemma distinct_pairs_and_app_cons :
    forall A R xs p ys l,
      l = (xs ++ p :: ys) ->
      distinct_pairs_and (A:=A) R l ->
      distinct_pairs_and R (xs ++ ys).
  Proof.
    induction xs; intros; subst; simpl in *; intuition eauto.
  Qed.

  Lemma distinct_pairs_and_app :
    forall A R l1 l2,
      distinct_pairs_and (A := A) R l1 ->
      distinct_pairs_and R l2 ->
      (forall x y,
         In x l1 ->
         In y l2 ->
         R x y) ->
      distinct_pairs_and R (l1 ++ l2).
  Proof.
    induction l1; intros; simpl in *; intuition.
    find_apply_lem_hyp in_app_or.
    intuition eauto.
  Qed.

  Theorem decomposition_invariant :
    inductive_invariant step_async step_async_init composed_invariant.
  Proof.
    unfold inductive_invariant. intuition.
    - unfold composed_invariant. simpl.
      intuition auto using state_invariant_init.
    - unfold inductive, composed_invariant. intros.
      match goal with H : step_async _ _ _ |- _ => invcs H end; intuition; simpl in *.
      + eauto using state_invariant_maintained_deliver.
      + find_apply_lem_hyp post_net_analyze_sent_packet.
        intuition
          eauto 10 using
              network_invariant_maintained_deliver_new,
              network_invariant_maintained_deliver_old,
              nw_nw_distinct_pairs_and_elim,
              network_network_invariant_sym.
      + apply distinct_pairs_and_app;
        eauto using network_network_invariant_maintained_deliver_new, distinct_pairs_and_app_cons.

        intros. do_in_map. subst.
        eapply network_network_invariant_maintained_deliver_old;
          eauto using nw_nw_distinct_pairs_and_elim.
        simpl; now rewrite <- surjective_pairing.
      + eauto using state_invariant_maintained_input.
      + find_apply_lem_hyp post_input_analyze_sent_packet.
        intuition
          eauto using network_invariant_maintained_input_new,
                      network_invariant_maintained_input_old.
      + apply distinct_pairs_and_app;
            eauto using network_network_invariant_maintained_input_new.
        intros.
        do_in_map. subst.
        apply network_network_invariant_sym.
        eapply network_network_invariant_maintained_input_old; eauto.
        simpl. now rewrite <- surjective_pairing.
  Qed.
End Decomposition.
