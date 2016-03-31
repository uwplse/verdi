Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.
Require Import ExtensionalUpdate.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".


Section SimulationUpdate.
  Context `{params : SimpleUpdateParams}.

  Variable first_update : handlerUpdate P.
  Variable first_update_first : Nth updates 0 first_update.

  Variable update_establishes_simulation :
    forall n update up failed net h out d ms,
      su_reachable_state (up, failed, net) ->
      up h = n ->
      Nth updates (S n) update ->
      huUpdate update h (nwState net h) = (out, d, ms) ->
      out = nil /\
      ms = nil.

  Variable input_handlers_preserve_simulations :
    forall n update1 update2 st h inp out d ms,
      su_reachable_state st ->
      Nth updates n update1 ->
      Nth updates (S n) update2 ->
      huInput update1 h inp (nwState (snd st) h) = (out, d, ms) ->
      huInput update2 h inp (snd (fst (huUpdate update2 h (nwState (snd st) h)))) =
      (out, snd (fst (huUpdate update2 h d)), ms).
      

  Lemma Nth_S_Nth :
    forall A (l : list A) n x,
      Nth l (S n) x ->
      exists y,
        Nth l n y.
  Proof.
    induction l.
    - intros.
      invcs H.
    - intros.
      invcs H.
      destruct n.
      + eexists; econstructor.
      + find_apply_hyp_hyp.
        break_exists_exists. constructor. auto.
  Qed.

  Inductive path : name -> nat -> data -> data -> Prop :=
  | pathO : forall h st, path h 0 st st
  | pathS :
      forall h n update st st',
        path h n st st' ->
        Nth updates (S n) update ->
        path h (S n) st (snd (fst (huUpdate update h st'))).

  Lemma path_unique :
    forall h n st sta stb,
      path h n st sta ->
      path h n st stb ->
      sta = stb.
  Proof.
    induction n; intros; simpl in *.
    - repeat match goal with
             | H : path _ _ _ _ |- _ =>
               invcs H
             end; auto.
    - repeat match goal with
             | H : path _ (S _) _ _ |- _ =>
               invcs H
             end; auto.
      repeat find_apply_lem_hyp Nth_nth_error.
      repeat find_rewrite.
      find_inversion.
      repeat f_equal. eauto.
  Qed.

  Lemma path_exists :
    forall h n update st,
      Nth updates n update ->
      exists st',
        path h n st st'.
  Proof.
    induction n; intros; simpl in *.
    - repeat econstructor.
    - find_copy_apply_lem_hyp Nth_S_Nth.
      break_exists.
      find_eapply_lem_hyp IHn.
      break_exists.
      repeat econstructor; eauto.
  Qed.

  Lemma su_reachable_state_extend :
    forall sigma sigma' tr,
      su_reachable_state sigma ->
      step_u sigma sigma' tr ->
      su_reachable_state sigma'.
  Proof.
    clear update_establishes_simulation.
    clear input_handlers_preserve_simulations.
    intros.
    unfold su_reachable_state in *.
    break_exists.
    eexists.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    apply refl_trans_n1_1n_trace.
    econstructor; eauto.
  Qed.

  
  Lemma reachable_path_exists :
    forall h n up sigma,
      Nth updates n up ->
      su_reachable_state sigma ->
      exists sigma',
        path h n (nwState (snd sigma) h) (nwState (snd sigma') h) /\
        su_reachable_state sigma'.
  Proof.
    induction n; intros; simpl in *.
    - exists sigma. intuition.
      constructor.
    - find_copy_apply_lem_hyp Nth_S_Nth.
      break_exists_name up'.
      find_eapply_lem_hyp IHn; eauto.
      break_exists_name sigma'.
      intuition.
      (* build the state *)
      remember (
          update (nwState (snd sigma')) h
                 (snd (fst (huUpdate up h (nwState (snd sigma') h))))
        ) as new_state.
      exists
        (update (fst (fst sigma')) h (S (fst (fst sigma') h)),
         snd (fst sigma'), {| nwPackets := nwPackets (snd sigma');
                              nwState := new_state|}).
      intuition.
      + subst; simpl. rewrite update_eq by auto.
        constructor; auto.
      + eapply su_reachable_state_extend; eauto.
        subst. destruct sigma'. destruct p.
        simpl. econstructor; eauto.
        
        
  Qed.
  
       (snd st') h) ->
      su_reachable_state st ->
      su_reachable_state st' ->
      Nth updates n update2 ->
      huInput first_update h inp (nwState (snd st) h) = (out, d, ms) ->
      huInput update2 h inp (nwState (snd st') h) = (out', d', ms') ->
      path h n d d' /\ out = out' /\ ms = ms'.
  Proof.
    induction n (* path *); intros; simpl in *.
    - match goal with
      | H : path _ _ _ _ |- _ =>
        invcs H
      end.
      repeat find_apply_lem_hyp Nth_nth_error.
      repeat find_rewrite.
      find_injection.
      repeat find_rewrite.
      tuple_inversion.
      intuition.
      constructor.
    - match goal with
      | H : path _ _ _ _ |- _ =>
        invcs H
      end.
      find_copy_apply_lem_hyp Nth_S_Nth.
      break_exists_name update1.
      remember (nwState (snd st)).
      destruct (huInput update1 h inp (nwState (snd st'0) h)) eqn:?.
      find_eapply_lem_hyp input_handlers_preserve_simulations; eauto.
      
      
  
  Definition equiv_states (st st' : (name -> nat) * list name * network) :=
    (forall h,
        path ((fst (fst st')) h) (nwState (snd st) h) (nwState (snd st') h)) /\
    snd (fst st) = snd (fst st') /\
    nwPackets (snd st) = nwPackets (snd st').
  
  Definition multi_updates := updates.

  Instance one_update_params : SimpleUpdateParams P :=
    { updates := [first_update] }.

  Notation step_one := (@step_u _ _ _ one_update_params).
  Notation step_multi := (@step_u _ _ _ params).
  Notation step_one_star := (@step_u_star _ _ _ one_update_params).
  Notation step_multi_star := (@step_u_star _ _ _ params).

  Definition is_reachable_equiv_state (st : (name -> nat) * list name * network) :=
    exists st' tr,
      step_one_star step_u_init st' tr /\
      equiv_states st' st.

  Definition step_multi_step_one :
    forall sto sto' stm trm tro tro',
      step_multi_star step_u_init stm trm ->
      step_one_star step_u_init sto tro ->
      step_one sto sto' tro' ->
      equiv_states sto stm ->
      exists stm' trm',
        equiv_states sto' stm' /\
        step_multi stm stm' trm'.
  Proof.
    intros.
    invcs H1.
    - match goal with
      | H : Nth [_] _ _ |- _ => invcs H; [|solve_by_inversion]
      end.
      
      


  Theorem is_reachable_equiv_state_inductive :
    inductive_invariant step_multi step_u_init is_reachable_equiv_state.
  Proof.
    unfold inductive_invariant.
    intuition;
      [(exists step_u_init, []); cbn; intuition;
       constructor; intuition; constructor|].
    unfold inductive. intros. invcs H0.
    - admit.
    - unfold is_reachable_equiv_state in *.
      break_exists_name st'; break_exists. intuition.
      destruct st', p.
      match goal with
      | H: context [equiv_states] |- _ =>
        unfold equiv_states in H
      end. simpl in *. intuition. subst.
      exists (n0, failed, {|
           nwPackets := map
                          (fun m : name * msg =>
                             {| pSrc := h; pDst := fst m; pBody := snd m |}) l ++
                          nwPackets n;
           nwState := fun nm : name => if name_eq_dec nm h then d else nwState n nm |}).
      exists x.
