Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.
Require Import ExtensionalUpdate.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".


Section SimulationUpdate.
  Context `{params : SimpleUpdateParams}.

  Variable first_update : handlerUpdate P.
  Variable first_update_first : Nth updates 0 first_update.

  Variable simulations :
    list (data -> data -> Prop).

  Variable simulations_valid :
    forall n update,
      Nth updates (S n) update ->
      exists simulation,
        Nth simulations n simulation.

  Variable update_establishes_simulation :
    forall n update up failed net h out d ms simulation,
      su_reachable_state (up, failed, net) ->
      up h = n ->
      Nth updates (S n) update ->
      huUpdate update h (nwState net h) = (out, d, ms) ->
      Nth simulations n simulation ->      
      out = nil /\
      ms = nil /\
      simulation (nwState net h) d.

  Variable input_handlers_preserve_simulations :
    forall n update1 update2 st st' h inp out d ms out' d' ms' simulation,
      su_reachable_state st ->
      su_reachable_state st' ->
      (fst (fst st)) h = n ->
      (fst (fst st')) h = S n ->
      Nth updates n update1 ->
      Nth updates (S n) update2 ->
      Nth simulations n simulation ->
      simulation (nwState (snd st) h) (nwState (snd st') h) ->
      huInput update1 h inp (nwState (snd st) h) = (out, d, ms) ->
      huInput update2 h inp (nwState (snd st') h) = (out', d', ms') ->
      simulation d d' /\ out = out' /\ ms = ms'.

  Inductive path : nat -> data -> data -> Prop :=
  | pathO : forall st, path 0 st st
  | pathS :
      forall n simulation st st' st'',
        path n st st' ->
        Nth simulations n simulation ->
        simulation st' st'' ->
        path (S n) st st''.

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
      
  Lemma input_handlers_preserve_paths :
    forall n update2 st st' h inp out d ms out' d' ms',
      path n (nwState (snd st) h) (nwState (snd st') h) ->
      su_reachable_state st ->
      su_reachable_state st' ->
      Nth updates n update2 ->
      huInput first_update h inp (nwState (snd st) h) = (out, d, ms) ->
      huInput update2 h inp (nwState (snd st') h) = (out', d', ms') ->
      path n d d' /\ out = out' /\ ms = ms'.
  Proof.
    induction n (* path *); intros; simpl in *;
      match goal with
      | H : path _ _ _ |- _ =>
        invcs H
      end.
    - repeat find_apply_lem_hyp Nth_nth_error.
      repeat find_rewrite.
      find_injection.
      repeat find_rewrite.
      tuple_inversion.
      intuition.
      constructor.
    - find_copy_apply_lem_hyp Nth_S_Nth.
      break_exists_name update1.
      
      
  
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
