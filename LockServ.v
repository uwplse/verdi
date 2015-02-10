Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import StatePacketPacketDecomposition.

Set Implicit Arguments.

Section LockServ.

  Variable num_Clients : nat.

  Definition Client_index := (fin num_Clients).

  Inductive Name :=
  | Client : Client_index -> Name
  | Server : Name.

  Definition list_Clients := map Client (all_fin num_Clients).

  Definition Name_eq_dec : forall a b : Name, {a = b} + {a <> b}.
    decide equality. apply fin_eq_dec.
  Qed.



  Inductive Msg :=
  | Lock   : Msg
  | Unlock : Msg
  | Locked : Msg.

  Definition Input := Msg.
  Definition Output := Msg.

  Definition Msg_eq_dec : forall a b : Msg, {a = b} + {a <> b}.
    decide equality.
  Qed.



  Record Data := mkData { queue : list Client_index ; held : bool }.

  Definition init_data (n : Name) : Data := mkData [] false.

  Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

  Definition ClientNetHandler (i : Client_index) (m : Msg) : Handler Data :=
    match m with
      | Locked => (put (mkData [] true)) >> write_output Locked
      | _ => nop
    end.

  Definition ClientIOHandler (i : Client_index) (m : Msg) : Handler Data :=
    match m with
      | Lock => send (Server, Lock)
      | Unlock => data <- get ;;
                  when (held data) (put (mkData [] false) >> send (Server, Unlock))
      | _ => nop
    end.

  Definition ServerNetHandler (src : Name) (m : Msg) : Handler Data :=
    st <- get ;;
    let q := queue st in
    match m with
      | Lock =>
        match src with
          | Server => nop
          | Client c =>
            when (null q) (send (src, Locked)) >> put (mkData (q++[c]) (held st))
        end
      | Unlock => match q with
                    | _ :: x :: xs => put (mkData (x :: xs) (held st)) >> send (Client x, Locked)
                    | _ => put (mkData [] (held st))
                  end
      | _ => nop
    end.

  Definition ServerIOHandler (m : Msg) : Handler Data := nop.

  Definition NetHandler (nm src : Name) (m : Msg) : Handler Data.
    destruct nm.
    - exact (ClientNetHandler c m).
    - exact (ServerNetHandler src m).
  Defined.

  Definition InputHandler (nm : Name) (m : Msg) : Handler Data.
    destruct nm.
    - exact (ClientIOHandler c m).
    - exact (ServerIOHandler m).
  Defined.

  Ltac handler_unfold :=
    repeat (monad_unfold; unfold NetHandler,
                                 InputHandler,
                                 ServerNetHandler,
                                 ClientNetHandler,
                                 ClientIOHandler,
                                 ServerIOHandler in *).



  Definition Nodes := Server :: list_Clients.

  Theorem In_n_Nodes :
    forall n : Name, In n Nodes.
  Proof.
    intros.
    unfold Nodes, list_Clients.
    simpl.
    destruct n.
    - right.
      apply in_map.
      apply all_fin_all.
    - left.
      reflexivity.
  Qed.

  Theorem nodup :
    NoDup Nodes.
  Proof.
    unfold Nodes, list_Clients.
    apply NoDup_cons.
    - in_crush. discriminate.
    - apply NoDup_map_injective.
      + intros. congruence.
      + apply all_fin_NoDup.
  Qed.



  Global Instance LockServ_BaseParams : BaseParams :=
    {
      data   := Data ;
      input  := Input ;
      output := Output
    }.

  Global Instance LockServ_MultiParams : MultiParams LockServ_BaseParams :=
    {
      name := Name ;
      msg  := Msg ;
      msg_eq_dec := Msg_eq_dec ;
      name_eq_dec := Name_eq_dec ;
      nodes := Nodes ;
      all_names_nodes := In_n_Nodes ;
      no_dup_nodes := nodup ;
      init_handlers := init_data ;
      net_handlers := fun dst src msg s =>
                        runGenHandler_ignore s (NetHandler dst src msg) ;
      input_handlers := fun nm msg s =>
                          runGenHandler_ignore s (InputHandler nm msg)
    }.



  (* This is the fundamental safety property of the system:
       No two different clients can (think they) hold
       the lock at once.
   *)
  Definition mutual_exclusion (sigma : name -> data) : Prop :=
    forall m n,
      held (sigma (Client m)) = true ->
      held (sigma (Client n)) = true ->
      m = n.

  (* The system enforces mutual exclusion at the server. Whenever a
     client believs it holds the lock, that client is at the head of the
     server's queue. *)
  Definition locks_correct (sigma : name -> data) : Prop :=
    forall n,
      held (sigma (Client n)) = true ->
      exists t,
        queue (sigma Server) = n :: t.

  (* We first show that this actually implies mutual exclusion. *)
  Lemma locks_correct_implies_mutex :
    forall sigma,
      locks_correct sigma ->
      mutual_exclusion sigma.
  Proof.
    unfold locks_correct, mutual_exclusion.
    intros.
    repeat match goal with
      | [ H : forall _, _ -> _, H' : _ |- _ ] =>
        apply H in H'
    end.
    break_exists.
    find_rewrite. find_inversion.
    auto.
  Qed.

  Definition valid_unlock q h c p :=
    pSrc p = Client c /\
    (exists t, q = c :: t) /\
    h = false.

  Definition locks_correct_unlock (sigma : name -> data) (p : packet) : Prop :=
    pBody p = Unlock ->
    exists c, valid_unlock (queue (sigma Server)) (held (sigma (Client c))) c p.

  Definition valid_locked q h c p :=
      pDst p = Client c /\
      (exists t, q = c :: t) /\
      h = false.

  Definition locks_correct_locked (sigma : name -> data) (p : packet) : Prop :=
    pBody p = Locked ->
    exists c, valid_locked (queue (sigma Server)) (held (sigma (Client c))) c p.


  Definition LockServ_network_invariant (sigma : name -> data) (p : packet) : Prop :=
    locks_correct_unlock sigma p /\
    locks_correct_locked sigma p.

  Definition LockServ_network_network_invariant (p q : packet) : Prop :=
    (pBody p = Unlock -> pBody q = Unlock -> False) /\
    (pBody p = Locked -> pBody q = Unlock -> False) /\
    (pBody p = Unlock -> pBody q = Locked -> False) /\
    (pBody p = Locked -> pBody q = Locked -> False).

  Lemma nwnw_sym :
    forall p q,
      LockServ_network_network_invariant p q ->
      LockServ_network_network_invariant q p.
  Proof.
    unfold LockServ_network_network_invariant.
    intuition.
  Qed.

  Lemma locks_correct_init :
    locks_correct init_handlers.
  Proof.
    unfold locks_correct. simpl. discriminate.
  Qed.

  Lemma InputHandler_cases :
    forall h i st u out st' ms,
      InputHandler h i st = (u, out, st', ms) ->
      (exists c, h = Client c /\
                 ((i = Lock /\ out = [] /\ st' = st /\ ms = [(Server, Lock)]) \/
                  (i = Unlock /\ out = [] /\ held st' = false /\
                   ((held st = true /\ ms = [(Server, Unlock)]) \/
                    (st' = st /\ ms = []))))) \/
      (out = [] /\ st' = st /\ ms = []).
  Proof.
    handler_unfold.
    intros.
    repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             end; subst; simpl in *; subst; simpl in *.
    - left. eexists. intuition.
    - left. eexists. intuition.
    - left. eexists. intuition.
    - subst. auto.
    - subst. auto.
  Qed.

  Lemma locks_correct_update_false :
    forall sigma st' x,
      locks_correct sigma ->
      held st' = false ->
      locks_correct (update sigma (Client x) st').
  Proof.
    unfold locks_correct.
    intuition.
    destruct (Name_eq_dec (Client x) (Client n)).
    - find_inversion. exfalso.
      rewrite_update.
      congruence.
    - rewrite_update.
      auto.
  Qed.

  Ltac set_up_input_handlers :=
    intros;
    find_apply_lem_hyp InputHandler_cases;
    intuition idtac; try break_exists; intuition idtac; subst;
    repeat find_rewrite;
    simpl in *; intuition idtac; repeat find_inversion;
    try now rewrite update_nop_ext.

  Lemma locks_correct_input_handlers :
    forall h i sigma u st' out ms,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct (update sigma h st').
  Proof.
    set_up_input_handlers;
    auto using locks_correct_update_false.
  Qed.

  Lemma ClientNetHandler_cases :
    forall c m st u out st' ms,
      ClientNetHandler c m st = (u, out, st', ms) ->
      ms = [] /\
      ((st' = st /\ out = [] ) \/
       (m = Locked /\ out = [Locked] /\ held st' = true)).
  Proof.
    handler_unfold.
    intros.
    repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             end; subst; auto.
  Qed.

  Lemma ServerNetHandler_cases :
    forall src m st u out st' ms,
      ServerNetHandler src m st = (u, out, st', ms) ->
      out = [] /\
      ((exists c, src = Client c /\
                  (m = Lock /\
                  queue st' = queue st ++ [c] /\
                  ((queue st = [] /\ ms = [(Client c, Locked)]) \/
                   (queue st <> [] /\ ms = [])))) \/
       ((m = Unlock /\
                   queue st' = tail (queue st) /\
                   ((queue st' = [] /\ ms = []) \/
                    (exists next t, queue st' = next :: t /\ ms = [(Client next, Locked)])))) \/
       ms = [] /\ st' = st).
  Proof.
    handler_unfold.
    intros.
    repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             end.
    - subst. subst. find_apply_lem_hyp null_sound. find_rewrite. simpl.
      intuition. left. eexists. intuition.
    - subst. subst. simpl. find_apply_lem_hyp null_false_neq_nil.
      intuition. left. eexists. intuition.
    - subst. subst. simpl. auto.
    - subst. subst. simpl. destruct st; simpl in *; subst; auto.
    - subst. subst. simpl in *. intuition.
    - subst. subst. simpl in *. intuition eauto.
    - subst. subst. simpl. intuition.
  Qed.

  Definition at_head_of_queue sigma c := (exists t, queue (sigma Server) = c :: t).

  Lemma at_head_of_queue_intro :
    forall sigma c t,
      queue (sigma Server) = c :: t ->
      at_head_of_queue sigma c.
  Proof.
    unfold at_head_of_queue.
    firstorder.
  Qed.

  Lemma locks_correct_update_true :
    forall sigma c st',
      held st' = true ->
      at_head_of_queue sigma c ->
      locks_correct sigma ->
      locks_correct (update sigma (Client c) st').
  Proof.
    unfold locks_correct.
    intros.
    destruct (Name_eq_dec (Client c) (Client n)); rewrite_update; try find_inversion; auto.
  Qed.

  Lemma locks_correct_locked_at_head :
    forall sigma p c,
      pDst p = Client c ->
      pBody p = Locked ->
      locks_correct_locked sigma p ->
      at_head_of_queue sigma c.
  Proof.
    unfold locks_correct_locked.
    firstorder.
    repeat find_rewrite. find_inversion.
    eauto using at_head_of_queue_intro.
  Qed.

  Lemma all_clients_false_locks_correct_server_update :
    forall sigma st,
      (forall c, held (sigma (Client c)) = false) ->
      locks_correct (update sigma Server st).
  Proof.
    unfold locks_correct.
    intros.
    rewrite_update.
    now find_higher_order_rewrite.
  Qed.

  Lemma locks_correct_true_at_head_of_queue :
    forall sigma x,
      locks_correct sigma ->
      held (sigma (Client x)) = true ->
      at_head_of_queue sigma x.
  Proof.
    unfold locks_correct.
    intros.
    find_apply_hyp_hyp. break_exists.
    eauto using at_head_of_queue_intro.
  Qed.

  Lemma at_head_of_nil :
    forall sigma c,
      at_head_of_queue sigma c ->
      queue (sigma Server) = [] ->
      False.
  Proof.
    unfold at_head_of_queue.
    firstorder.
    congruence.
  Qed.

  Lemma empty_queue_all_clients_false :
    forall sigma,
      locks_correct sigma ->
      queue (sigma Server) = [] ->
      (forall c, held (sigma (Client c)) = false).
  Proof.
    intuition.
    destruct (held (sigma (Client c))) eqn:?; auto.
    exfalso. eauto using at_head_of_nil, locks_correct_true_at_head_of_queue.
  Qed.

  Lemma unlock_in_flight_all_clients_false :
    forall sigma p,
      pBody p = Unlock ->
      locks_correct_unlock sigma p ->
      locks_correct sigma ->
      (forall c, held (sigma (Client c)) = false).
  Proof.
    intros.
    destruct (held (sigma (Client c))) eqn:?; auto.
    firstorder.
    find_copy_apply_lem_hyp locks_correct_true_at_head_of_queue; auto.
    unfold at_head_of_queue in *. break_exists.
    congruence.
  Qed.

  Lemma locks_correct_at_head_preserved :
    forall sigma st',
      locks_correct sigma ->
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update sigma Server st') c) ->
      locks_correct (update sigma Server st').
  Proof.
    unfold locks_correct, at_head_of_queue.
    firstorder.
    rewrite_update.
    eauto.
  Qed.

  Lemma snoc_at_head_of_queue_preserved :
    forall sigma st' x,
      queue st' = queue (sigma Server) ++ [x] ->
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update sigma Server st') c).
  Proof.
    unfold at_head_of_queue.
    intuition. break_exists.
    rewrite_update.
    find_rewrite.
    eauto.
  Qed.

  Ltac set_up_net_handlers :=
    intros;
    match goal with
      | [ H : context [ NetHandler (pDst ?p) _ _ _ ] |- _ ] =>
        destruct (pDst p) eqn:?
    end; simpl in *;
    [find_apply_lem_hyp ClientNetHandler_cases |
     find_apply_lem_hyp ServerNetHandler_cases; intuition; try break_exists ];
    intuition; subst;
    simpl in *; intuition;
    repeat find_rewrite;
    repeat find_inversion;
    simpl in *;
    try now rewrite update_nop_ext.


  Lemma locks_correct_net_handlers :
    forall p sigma u st' out ms,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_unlock sigma p ->
      locks_correct_locked sigma p ->
      locks_correct (update sigma (pDst p) st').
  Proof.
    set_up_net_handlers;
    eauto using
          locks_correct_update_true, locks_correct_locked_at_head,
          all_clients_false_locks_correct_server_update, empty_queue_all_clients_false,
          locks_correct_at_head_preserved, snoc_at_head_of_queue_preserved,
          all_clients_false_locks_correct_server_update, unlock_in_flight_all_clients_false.
  Qed.

  Lemma locks_correct_unlock_sent_lock :
    forall sigma p,
      pBody p = Lock ->
      locks_correct_unlock sigma p.
  Proof.
    unfold locks_correct_unlock.
    intuition. congruence.
  Qed.

  Lemma locks_correct_unlock_sent_locked :
    forall sigma p,
      pBody p = Locked ->
      locks_correct_unlock sigma p.
  Proof.
    unfold locks_correct_unlock.
    intuition. congruence.
  Qed.

  Lemma locks_correct_unlock_input_handlers_old :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_unlock sigma p ->
      locks_correct_unlock (update sigma h st') p.
  Proof.
    set_up_input_handlers.
    destruct (pBody p) eqn:?.
    - auto using locks_correct_unlock_sent_lock.
    - now erewrite unlock_in_flight_all_clients_false in * by eauto.
    - auto using locks_correct_unlock_sent_locked.
  Qed.

  Lemma locked_in_flight_all_clients_false :
    forall sigma p,
      pBody p = Locked ->
      locks_correct_locked sigma p ->
      locks_correct sigma ->
      (forall c, held (sigma (Client c)) = false).
  Proof.
    intros.
    destruct (held (sigma (Client c))) eqn:?; auto.
    firstorder.
    find_copy_apply_lem_hyp locks_correct_true_at_head_of_queue; auto.
    unfold at_head_of_queue in *. break_exists.
    congruence.
  Qed.

  Lemma locks_correct_locked_sent_lock :
    forall sigma p,
      pBody p = Lock ->
      locks_correct_locked sigma p.
  Proof.
    unfold locks_correct_locked.
    intuition. congruence.
  Qed.

  Lemma locks_correct_locked_sent_unlock :
    forall sigma p,
      pBody p = Unlock ->
      locks_correct_locked sigma p.
  Proof.
    unfold locks_correct_locked.
    intuition. congruence.
  Qed.

  Lemma locks_correct_locked_input_handlers_old :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_locked sigma p ->
      locks_correct_locked (update sigma h st') p.
  Proof.
    set_up_input_handlers.
    destruct (pBody p) eqn:?.
    - auto using locks_correct_locked_sent_lock.
    - auto using locks_correct_locked_sent_unlock.
    - now erewrite locked_in_flight_all_clients_false in * by eauto.
  Qed.

  Lemma locks_correct_unlock_true_to_false :
    forall sigma p x st',
      at_head_of_queue sigma x ->
      held st' = false ->
      pSrc p = Client x ->
      locks_correct_unlock (update sigma (Client x) st') p.
  Proof.
    unfold locks_correct_unlock, valid_unlock.
    intros.
    exists x.
    intuition; now rewrite_update.
  Qed.

  Lemma locks_correct_unlock_input_handlers_new :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      In (pDst p, pBody p) ms ->
      pSrc p = h ->
      locks_correct_unlock (update sigma h st') p.
  Proof.
    set_up_input_handlers;

    auto using locks_correct_unlock_sent_lock,
               locks_correct_unlock_true_to_false,
               locks_correct_true_at_head_of_queue.
  Qed.

  Lemma locks_correct_locked_input_handlers_new :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      In (pDst p, pBody p) ms ->
      locks_correct_locked (update sigma h st') p.
  Proof.
    set_up_input_handlers;
    auto using locks_correct_locked_sent_lock, locks_correct_locked_sent_unlock.
  Qed.

  Lemma nwnw_locked_lock :
    forall p q,
      LockServ_network_network_invariant p q ->
      pBody p = Locked ->
      pBody q = Lock.
  Proof.
    unfold LockServ_network_network_invariant.
    intros.
    destruct (pBody q); intuition; try discriminate.
  Qed.

  Lemma nwnw_unlock_lock :
    forall p q,
      LockServ_network_network_invariant p q ->
      pBody p = Unlock ->
      pBody q = Lock.
  Proof.
    unfold LockServ_network_network_invariant.
    intros.
    destruct (pBody q); intuition; try discriminate.
  Qed.

  Lemma locks_correct_unlock_at_head :
    forall sigma p c,
      pSrc p = Client c ->
      pBody p = Unlock ->
      locks_correct_unlock sigma p ->
      at_head_of_queue sigma c.
  Proof.
    unfold locks_correct_unlock.
    intros.
    find_apply_hyp_hyp. clear H1.
    break_exists.
    unfold valid_unlock in *. intuition.
    break_exists.
    repeat find_rewrite. repeat find_inversion.
    eauto using at_head_of_queue_intro.
  Qed.

  Lemma locks_correct_unlock_at_head_preserved :
    forall sigma st' p,
      locks_correct_unlock sigma p ->
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update sigma Server st') c) ->
      locks_correct_unlock (update sigma Server st') p.
  Proof.
    unfold locks_correct_unlock, valid_unlock.
    intuition.
    break_exists.
    exists x.
    intuition.
    - firstorder.
    - now rewrite_update.
  Qed.

  Lemma nil_at_head_of_queue_preserved :
    forall c sigma sigma',
      queue (sigma Server) = [] ->
      at_head_of_queue sigma c ->
      at_head_of_queue sigma' c.
  Proof.
    unfold at_head_of_queue.
    firstorder.
    congruence.
  Qed.

  Lemma locks_correct_unlock_net_handlers_old :
    forall p sigma u st' out ms q,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_unlock sigma q ->
      LockServ_network_network_invariant p q ->
      locks_correct_unlock (update sigma (pDst p) st') q.
  Proof.
    set_up_net_handlers;
    eauto using locks_correct_unlock_sent_lock, nwnw_locked_lock,
                locks_correct_unlock_at_head_preserved, snoc_at_head_of_queue_preserved,
                nwnw_unlock_lock, nil_at_head_of_queue_preserved.
  Qed.

  Lemma locks_correct_locked_at_head_preserved :
    forall sigma st' p,
      locks_correct_locked sigma p ->
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update sigma Server st') c) ->
      locks_correct_locked (update sigma Server st') p.
  Proof.
    unfold locks_correct_locked, valid_locked.
    intuition.
    break_exists.
    exists x.
    intuition.
    - firstorder.
    - now rewrite_update.
  Qed.

  Lemma locks_correct_locked_net_handlers_old :
    forall p sigma u st' out ms q,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_locked sigma q ->
      LockServ_network_network_invariant p q ->
      locks_correct_locked (update sigma (pDst p) st') q.
  Proof.
    set_up_net_handlers;
    eauto using locks_correct_locked_sent_lock, nwnw_locked_lock,
      locks_correct_locked_at_head_preserved, snoc_at_head_of_queue_preserved,
      nwnw_unlock_lock, nil_at_head_of_queue_preserved.
  Qed.

  Lemma locks_correct_unlock_net_handlers_new :
    forall p sigma u st' out ms q,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      In (pDst q, pBody q) ms ->
      locks_correct_unlock (update sigma (pDst p) st') q.
  Proof.
    set_up_net_handlers;
    auto using locks_correct_unlock_sent_locked.
  Qed.

  Lemma locks_correct_locked_intro :
    forall sigma p c t st',
      pDst p = Client c ->
      held (sigma (Client c)) = false ->
      queue st' = c :: t ->
      locks_correct_locked (update sigma Server st') p.
  Proof.
    unfold locks_correct_locked, valid_locked.
    intros.
    exists c.
    intuition.
    - exists t. now rewrite_update.
    - now rewrite_update.
  Qed.

  Lemma locks_correct_locked_net_handlers_new :
    forall p sigma u st' out ms q,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_unlock sigma p ->
      In (pDst q, pBody q) ms ->
      locks_correct_locked (update sigma (pDst p) st') q.
  Proof.
    set_up_net_handlers;
    eauto using locks_correct_locked_intro,
                empty_queue_all_clients_false,
                unlock_in_flight_all_clients_false.
  Qed.

  Lemma nwnw_lock :
    forall p p',
      pBody p = Lock ->
      LockServ_network_network_invariant p p'.
  Proof.
    unfold LockServ_network_network_invariant.
    intuition; simpl in *; congruence.
  Qed.

  Lemma LockServ_nwnw_input_handlers_old_new :
    forall h i sigma u st' out ms p p',
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      LockServ_network_invariant sigma p ->
      In (pDst p', pBody p') ms ->
      pSrc p' = h ->
      LockServ_network_network_invariant p p'.
  Proof.
    unfold LockServ_network_invariant.
    set_up_input_handlers.
    - auto using nwnw_sym, nwnw_lock.
    - destruct (pBody p) eqn:?.
      + auto using nwnw_lock.
      + now erewrite unlock_in_flight_all_clients_false in * by eauto.
      + now erewrite locked_in_flight_all_clients_false in * by eauto.
  Qed.

  Lemma LockServ_nwnw_input_handlers_new_new :
    forall h i sigma u st' out ms,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      distinct_pairs_and LockServ_network_network_invariant
                         (map (fun m => mkPacket h (fst m) (snd m)) ms).
  Proof.
    set_up_input_handlers.
  Qed.

  Lemma nw_empty_queue_lock :
    forall sigma p,
      LockServ_network_invariant sigma p ->
      queue (sigma Server) = [] ->
      pBody p = Lock.
  Proof.
    unfold LockServ_network_invariant,
    locks_correct_unlock, locks_correct_locked,
    valid_unlock, valid_locked.
    intuition.
    destruct (pBody p) eqn:?; intuition; break_exists; intuition; break_exists;
    congruence.
  Qed.

  Lemma LockServ_nwnw_net_handlers_old_new :
    forall p sigma u st' out ms q p',
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      LockServ_network_invariant sigma p ->
      LockServ_network_invariant sigma q ->
      LockServ_network_network_invariant p q ->
      In (pDst p', pBody p') ms ->
      LockServ_network_network_invariant p' q.
  Proof.
    set_up_net_handlers;
    eauto using nwnw_sym, nwnw_lock, nw_empty_queue_lock, nwnw_unlock_lock.
  Qed.

  Lemma LockServ_nwnw_net_handlers_new_new :
    forall p sigma u st' out ms,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) ->
      locks_correct sigma ->
      LockServ_network_invariant sigma p ->
      distinct_pairs_and LockServ_network_network_invariant
                         (map (fun m => mkPacket (pDst p) (fst m) (snd m)) ms).
  Proof.
    set_up_net_handlers.
  Qed.

  Instance LockServ_Decompositition : Decomposition _ LockServ_MultiParams.
  apply Build_Decomposition with (state_invariant := locks_correct)
                                 (network_invariant := LockServ_network_invariant)
                                 (network_network_invariant := LockServ_network_network_invariant);
    simpl; intros; monad_unfold; repeat break_let; repeat find_inversion.
  - auto using nwnw_sym.
  - auto using locks_correct_init.
  - eauto using locks_correct_input_handlers.
  - unfold LockServ_network_invariant in *. intuition.
    eauto using locks_correct_net_handlers.
  - unfold LockServ_network_invariant in *.
    intuition eauto using locks_correct_unlock_input_handlers_old,
                          locks_correct_locked_input_handlers_old.
  - unfold LockServ_network_invariant in *.
    intuition eauto using locks_correct_unlock_input_handlers_new,
                          locks_correct_locked_input_handlers_new.
  - unfold LockServ_network_invariant in *.
    intuition eauto using locks_correct_unlock_net_handlers_old,
                          locks_correct_locked_net_handlers_old.
  - unfold LockServ_network_invariant in *.
    intuition eauto using locks_correct_unlock_net_handlers_new,
                          locks_correct_locked_net_handlers_new.
  - eauto using LockServ_nwnw_input_handlers_old_new.
  - eauto using LockServ_nwnw_input_handlers_new_new.
  - eauto using LockServ_nwnw_net_handlers_old_new.
  - eauto using LockServ_nwnw_net_handlers_new_new.
  Qed.
End LockServ.
