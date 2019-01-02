Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import StructTact.Fin.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import Verdi.StatePacketPacketDecomposition.

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

  Definition Msg_eq_dec : forall a b : Msg, {a = b} + {a <> b}.
    decide equality.
  Qed.
    
  Definition Input := Msg.
  Definition Output := Msg.

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

  Definition NetHandler (nm src : Name) (m : Msg) : Handler Data :=
    match nm with
      | Client c => ClientNetHandler c m
      | Server   => ServerNetHandler src m
    end.

  Definition InputHandler (nm : Name) (m : Msg) : Handler Data :=
    match nm with
      | Client c => ClientIOHandler c m
      | Server   => ServerIOHandler m
    end.

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
  Proof using.
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
  Proof using.
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
  Proof using.
    unfold locks_correct, mutual_exclusion.
    intros.
    repeat find_apply_hyp_hyp.
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
  Proof using.
    unfold LockServ_network_network_invariant.
    intuition.
  Qed.

  Lemma locks_correct_init :
    locks_correct init_handlers.
  Proof using.
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
  Proof using.
    handler_unfold.
    intros.
    repeat break_match; repeat tuple_inversion;
      subst; simpl in *; subst; simpl in *.
    - left. eexists. intuition.
    - left. eexists. intuition.
    - left. eexists. intuition.
    - auto.
    - auto.
  Qed.

  Lemma locks_correct_update_false :
    forall sigma st' x,
      locks_correct sigma ->
      held st' = false ->
      locks_correct (update name_eq_dec sigma (Client x) st').
  Proof using.
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
      locks_correct (update name_eq_dec sigma h st').
  Proof using.
    set_up_input_handlers;
    auto using locks_correct_update_false.
  Qed.

  Lemma ClientNetHandler_cases :
    forall c m st u out st' ms,
      ClientNetHandler c m st = (u, out, st', ms) ->
      ms = [] /\
      ((st' = st /\ out = [] ) \/
       (m = Locked /\ out = [Locked] /\ held st' = true)).
  Proof using.
    handler_unfold.
    intros.
    repeat break_match; repeat tuple_inversion; subst; auto.
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
  Proof using.
    handler_unfold.
    intros.
    repeat break_match; repeat tuple_inversion; subst.
    - find_apply_lem_hyp null_sound. find_rewrite. simpl.
      intuition. left. eexists. intuition.
    - simpl. find_apply_lem_hyp null_false_neq_nil.
      intuition. left. eexists. intuition.
    - simpl. auto.
    - simpl. destruct st; simpl in *; subst; auto.
    - simpl in *. intuition.
    - simpl in *. intuition eauto.
    - simpl. intuition.
  Qed.

  Definition at_head_of_queue sigma c := (exists t, queue (sigma Server) = c :: t).

  Lemma at_head_of_queue_intro :
    forall sigma c t,
      queue (sigma Server) = c :: t ->
      at_head_of_queue sigma c.
  Proof using.
    unfold at_head_of_queue.
    firstorder.
  Qed.

  Lemma locks_correct_update_true :
    forall sigma c st',
      held st' = true ->
      at_head_of_queue sigma c ->
      locks_correct sigma ->
      locks_correct (update name_eq_dec sigma (Client c) st').
  Proof using.
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
  Proof using.
    unfold locks_correct_locked.
    firstorder.
    repeat find_rewrite. find_inversion.
    eauto using at_head_of_queue_intro.
  Qed.

  Lemma all_clients_false_locks_correct_server_update :
    forall sigma st,
      (forall c, held (sigma (Client c)) = false) ->
      locks_correct (update name_eq_dec sigma Server st).
  Proof using.
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
  Proof using.
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
  Proof using.
    unfold at_head_of_queue.
    firstorder.
    congruence.
  Qed.

  Lemma empty_queue_all_clients_false :
    forall sigma,
      locks_correct sigma ->
      queue (sigma Server) = [] ->
      (forall c, held (sigma (Client c)) = false).
  Proof using.
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
  Proof using.
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
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update name_eq_dec sigma Server st') c) ->
      locks_correct (update name_eq_dec sigma Server st').
  Proof using.
    unfold locks_correct, at_head_of_queue.
    firstorder.
    rewrite_update.
    eauto.
  Qed.

  Lemma snoc_at_head_of_queue_preserved :
    forall sigma st' x,
      queue st' = queue (sigma Server) ++ [x] ->
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update name_eq_dec sigma Server st') c).
  Proof using.
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
      locks_correct (update name_eq_dec sigma (pDst p) st').
  Proof using.
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
  Proof using.
    unfold locks_correct_unlock.
    intuition. congruence.
  Qed.

  Lemma locks_correct_unlock_sent_locked :
    forall sigma p,
      pBody p = Locked ->
      locks_correct_unlock sigma p.
  Proof using.
    unfold locks_correct_unlock.
    intuition. congruence.
  Qed.

  Lemma locks_correct_unlock_input_handlers_old :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_unlock sigma p ->
      locks_correct_unlock (update name_eq_dec sigma h st') p.
  Proof using.
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
  Proof using.
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
  Proof using.
    unfold locks_correct_locked.
    intuition. congruence.
  Qed.

  Lemma locks_correct_locked_sent_unlock :
    forall sigma p,
      pBody p = Unlock ->
      locks_correct_locked sigma p.
  Proof using.
    unfold locks_correct_locked.
    intuition. congruence.
  Qed.

  Lemma locks_correct_locked_input_handlers_old :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      locks_correct sigma ->
      locks_correct_locked sigma p ->
      locks_correct_locked (update name_eq_dec sigma h st') p.
  Proof using.
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
      locks_correct_unlock (update name_eq_dec sigma (Client x) st') p.
  Proof using.
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
      locks_correct_unlock (update name_eq_dec sigma h st') p.
  Proof using.
    set_up_input_handlers;

    auto using locks_correct_unlock_sent_lock,
               locks_correct_unlock_true_to_false,
               locks_correct_true_at_head_of_queue.
  Qed.

  Lemma locks_correct_locked_input_handlers_new :
    forall h i sigma u st' out ms p,
      InputHandler h i (sigma h) = (u, out, st', ms) ->
      In (pDst p, pBody p) ms ->
      locks_correct_locked (update name_eq_dec sigma h st') p.
  Proof using.
    set_up_input_handlers;
    auto using locks_correct_locked_sent_lock, locks_correct_locked_sent_unlock.
  Qed.

  Lemma nwnw_locked_lock :
    forall p q,
      LockServ_network_network_invariant p q ->
      pBody p = Locked ->
      pBody q = Lock.
  Proof using.
    unfold LockServ_network_network_invariant.
    intros.
    destruct (pBody q); intuition; try discriminate.
  Qed.

  Lemma nwnw_unlock_lock :
    forall p q,
      LockServ_network_network_invariant p q ->
      pBody p = Unlock ->
      pBody q = Lock.
  Proof using.
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
  Proof using.
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
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update name_eq_dec sigma Server st') c) ->
      locks_correct_unlock (update name_eq_dec sigma Server st') p.
  Proof using.
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
  Proof using.
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
      locks_correct_unlock (update name_eq_dec sigma (pDst p) st') q.
  Proof using.
    set_up_net_handlers;
    eauto using locks_correct_unlock_sent_lock, nwnw_locked_lock,
                locks_correct_unlock_at_head_preserved, snoc_at_head_of_queue_preserved,
                nwnw_unlock_lock, nil_at_head_of_queue_preserved.
  Qed.

  Lemma locks_correct_locked_at_head_preserved :
    forall sigma st' p,
      locks_correct_locked sigma p ->
      (forall c, at_head_of_queue sigma c -> at_head_of_queue (update name_eq_dec sigma Server st') c) ->
      locks_correct_locked (update name_eq_dec sigma Server st') p.
  Proof using.
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
      locks_correct_locked (update name_eq_dec sigma (pDst p) st') q.
  Proof using.
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
      locks_correct_unlock (update name_eq_dec sigma (pDst p) st') q.
  Proof using.
    set_up_net_handlers;
    auto using locks_correct_unlock_sent_locked.
  Qed.

  Lemma locks_correct_locked_intro :
    forall sigma p c t st',
      pDst p = Client c ->
      held (sigma (Client c)) = false ->
      queue st' = c :: t ->
      locks_correct_locked (update name_eq_dec sigma Server st') p.
  Proof using.
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
      locks_correct_locked (update name_eq_dec sigma (pDst p) st') q.
  Proof using.
    set_up_net_handlers;
    eauto using locks_correct_locked_intro,
                empty_queue_all_clients_false,
                unlock_in_flight_all_clients_false.
  Qed.

  Lemma nwnw_lock :
    forall p p',
      pBody p = Lock ->
      LockServ_network_network_invariant p p'.
  Proof using.
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
  Proof using.
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
  Proof using.
    set_up_input_handlers.
  Qed.

  Lemma nw_empty_queue_lock :
    forall sigma p,
      LockServ_network_invariant sigma p ->
      queue (sigma Server) = [] ->
      pBody p = Lock.
  Proof using.
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
  Proof using.
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
  Proof using.
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
  Defined.

  Theorem true_in_reachable_mutual_exclusion :
    true_in_reachable step_async step_async_init (fun net => mutual_exclusion (nwState net)).
  Proof using.
    pose proof decomposition_invariant.
    find_apply_lem_hyp inductive_invariant_true_in_reachable.
    unfold true_in_reachable in *.
    intros.
    apply locks_correct_implies_mutex.
    match goal with
    | [ H : _ |- _ ] => apply H
    end.
    auto.
  Qed.

  Fixpoint last_holder' (holder : option Client_index) (trace : list (name * (input + list output))) : option Client_index :=
    match trace with
      | [] => holder
      | (Client n, inl Unlock) :: tr => match holder with
                                          | None => last_holder' holder tr
                                          | Some m => if fin_eq_dec _ n m
                                                      then last_holder' None tr
                                                      else last_holder' holder tr
                                        end

      | (Client n, inr [Locked]) :: tr => last_holder' (Some n) tr
      | (n, _) :: tr => last_holder' holder tr
    end.

  Fixpoint trace_mutual_exclusion' (holder : option Client_index) (trace : list (name * (input + list output))) : Prop :=
    match trace with
      | [] => True
      | (Client n, (inl Unlock)) :: tr' => match holder with
                                             | Some m => if fin_eq_dec _ n m
                                                         then trace_mutual_exclusion' None tr'
                                                         else trace_mutual_exclusion' holder tr'
                                             | _ => trace_mutual_exclusion' holder tr'
                                           end
      | (n, (inl _)) :: tr' => trace_mutual_exclusion' holder tr'
      | (Client n, (inr [Locked])) :: tr' => match holder with
                                               | None => trace_mutual_exclusion' (Some n) tr'
                                               | Some _ => False
                                             end
      | (_, (inr [])) :: tr' => trace_mutual_exclusion' holder tr'
      | (_, (inr _)) :: tr' => False
    end.

  Definition trace_mutual_exclusion (trace : list (name * (input + list output))) : Prop :=
    trace_mutual_exclusion' None trace.

  Definition last_holder (trace : list (name * (input + list output))) : option Client_index :=
    last_holder' None trace.

  Lemma cross_relation :
    forall (P : network -> list (name * (input + list output)) -> Prop),
      P step_async_init [] ->
      (forall st st' tr ev,
         step_async_star step_async_init st tr ->
         P st tr ->
         step_async st st' ev ->
         P st' (tr ++ ev)) ->
      forall st tr,
        step_async_star step_async_init st tr ->
        P st tr.
  Proof using.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H1.
    induction H1; intros; subst; eauto.
    eapply H3; eauto.
    - apply refl_trans_n1_1n_trace. auto.
    - apply IHrefl_trans_n1_trace; auto.
  Qed.

  Lemma trace_mutex'_no_out_extend :
    forall tr n h,
      trace_mutual_exclusion' h tr ->
      trace_mutual_exclusion' h (tr ++ [(n, inr [])]).
  Proof using.
    induction tr; intuition; unfold trace_mutual_exclusion in *; simpl in *;
    repeat break_match; subst; intuition.
  Qed.

  Lemma last_holder'_no_out_inv :
    forall tr h c n,
      last_holder' h (tr ++ [(c, inr [])]) = Some n ->
      last_holder' h tr = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; subst; intuition; eauto.
  Qed.

  Lemma last_holder'_no_out_extend :
    forall tr h c n,
      last_holder' h tr = Some n ->
      last_holder' h (tr ++ [(c, inr [])]) = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; subst; intuition.
  Qed.

  Lemma decomposition_reachable_nw_invariant :
    forall st tr p,
      step_async_star step_async_init st tr ->
      In p (nwPackets st) ->
      network_invariant (nwState st) p.
  Proof using.
    pose proof decomposition_invariant.
    find_apply_lem_hyp inductive_invariant_true_in_reachable.
    unfold true_in_reachable, reachable in *.
    intuition.
    unfold composed_invariant in *.
    apply H; eauto.
  Qed.

  Lemma trace_mutex'_locked_extend :
    forall tr h n,
      trace_mutual_exclusion' h tr ->
      last_holder' h tr = None ->
      trace_mutual_exclusion' h (tr ++ [(Client n, inr [Locked])]).
  Proof using.
    induction tr; intros; simpl in *.
    - subst. auto.
    - simpl in *. repeat break_match; subst; intuition.
  Qed.

  Lemma reachable_intro :
    forall a tr,
      step_async_star step_async_init a tr ->
      reachable step_async step_async_init a.
  Proof using.
    unfold reachable.
    intros. eauto.
  Qed.

  Lemma locks_correct_locked_invariant :
    forall st p,
      reachable step_async step_async_init st ->
      In p (nwPackets st) ->
      locks_correct_locked (nwState st) p.
  Proof using.
    intros.
    pose proof decomposition_invariant.
    find_apply_lem_hyp inductive_invariant_true_in_reachable.
    unfold true_in_reachable in *. apply H1; auto.
  Qed.

  Lemma locks_correct_invariant :
    forall st,
      reachable step_async step_async_init st ->
      locks_correct (nwState st).
  Proof using.
    intros.
    pose proof decomposition_invariant.
    find_apply_lem_hyp inductive_invariant_true_in_reachable.
    unfold true_in_reachable in *. apply H0; auto.
  Qed.

  Lemma mutual_exclusion_invariant :
    forall st,
      reachable step_async step_async_init st ->
      mutual_exclusion (nwState st).
  Proof using.
    intros.
    apply locks_correct_implies_mutex.
    auto using locks_correct_invariant.
  Qed.

  Lemma last_holder'_locked_some_eq :
    forall tr h c n,
      last_holder' h (tr ++ [(Client c, inr [Locked])]) = Some n ->
      c = n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; subst; eauto.
    congruence.
  Qed.

  Ltac my_update_destruct :=
    match goal with
      | [H : context [ update _ _ ?x _ ?y ] |- _ ] => destruct (Name_eq_dec x y)
      | [ |- context [ update _ _ ?x _ ?y ] ] => destruct (Name_eq_dec x y)
    end.

  Lemma last_holder'_server_extend :
    forall tr h i,
      last_holder' h (tr ++ [(Server, inl i)]) = last_holder' h tr.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; auto.
  Qed.

  Lemma last_holder'_locked_extend :
    forall tr h n,
      last_holder' h (tr ++ [(Client n, inr [Locked])]) = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; auto.
  Qed.

  Lemma trace_mutual_exclusion'_extend_input :
    forall tr h c i,
      i <> Unlock ->
      trace_mutual_exclusion' h tr ->
      trace_mutual_exclusion' h (tr ++ [(Client c, inl i)]).
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; intuition.
  Qed.

  Lemma trace_mutual_exclusion'_extend_input_server :
    forall tr h i,
      trace_mutual_exclusion' h tr ->
      trace_mutual_exclusion' h (tr ++ [(Server, inl i)]).
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; intuition.
  Qed.

  Lemma last_holder'_input_inv :
    forall tr h c i n,
      i <> Unlock ->
      last_holder' h (tr ++ [(Client c, inl i)]) = Some n ->
      last_holder' h tr = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; auto; try congruence; subst; eauto.
  Qed.

  Lemma last_holder'_input_inv_server :
    forall tr h i n,
      last_holder' h (tr ++ [(Server, inl i)]) = Some n ->
      last_holder' h tr = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; auto; try congruence; subst; eauto.
  Qed.

  Lemma last_holder'_input_extend :
    forall tr h c i n,
      i <> Unlock ->
      last_holder' h tr = Some n ->
      last_holder' h (tr ++ [(Client c, inl i)]) = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; auto.
    congruence.
  Qed.

  Lemma trace_mutex'_unlock_extend :
    forall tr h c,
      trace_mutual_exclusion' h tr ->
      trace_mutual_exclusion' h (tr ++ [(Client c, inl Unlock)]).
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; intuition (auto; try congruence).
  Qed.

  Lemma last_holder'_unlock_none :
    forall tr h c,
      last_holder' h tr = Some c ->
      last_holder' h (tr ++ [(Client c, inl Unlock)]) = None.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; intuition.
    congruence.
  Qed.

  Lemma last_holder_unlock_none :
    forall tr c,
      last_holder tr = Some c ->
      last_holder (tr ++ [(Client c, inl Unlock)]) = None.
  Proof using.
    intros.
    apply last_holder'_unlock_none. auto.
  Qed.

  Lemma last_holder_some_unlock_inv :
    forall tr h c n,
      last_holder' h (tr ++ [(Client c, inl Unlock)]) = Some n ->
      last_holder' h tr = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; subst;
    intuition; try congruence; eauto.
  Qed.

  Lemma last_holder'_neq_unlock_extend :
    forall tr h n c,
      last_holder' h tr = Some n ->
      n <> c ->
      last_holder' h (tr ++ [(Client c, inl Unlock)]) = Some n.
  Proof using.
    induction tr; intros; simpl in *; repeat break_match; subst; try congruence; intuition.
  Qed.

  Lemma LockServ_mutual_exclusion_trace :
    forall st tr,
      step_async_star step_async_init st tr ->
      trace_mutual_exclusion tr /\
      (forall n, last_holder tr = Some n -> held (nwState st (Client n)) = true) /\
      (forall n, held (nwState st (Client n)) = true -> last_holder tr = Some n).
  Proof using.
    apply cross_relation; intros.
    - intuition.
      + red. red. auto.
      + unfold last_holder in *. simpl in *. discriminate.
      + unfold last_holder in *. simpl in *. discriminate.
    - match goal with
        | [ H : step_async _ _ _ |- _ ] => invcs H
      end; monad_unfold; repeat break_let; repeat find_inversion.
      + unfold NetHandler in *. break_match.
        * find_apply_lem_hyp ClientNetHandler_cases.
          break_and.
          { break_or_hyp.
            - intuition; subst.
              + apply trace_mutex'_no_out_extend; auto.
              + rewrite update_nop_ext.
                find_apply_lem_hyp last_holder'_no_out_inv.
                auto.
              + match goal with
                  | [ H : _ |- _ ] => rewrite update_nop in H
                end.
                find_apply_hyp_hyp.
                apply last_holder'_no_out_extend. auto.
            - intuition; subst.
              + apply trace_mutex'_locked_extend. auto.
                destruct (last_holder' None tr) eqn:?; auto.
                find_apply_hyp_hyp.
                erewrite locked_in_flight_all_clients_false in * by
                  eauto using locks_correct_locked_invariant, reachable_intro,
                              locks_correct_invariant.
                discriminate.
              + my_update_destruct; try find_inversion; rewrite_update; auto.
                find_apply_lem_hyp last_holder'_locked_some_eq. congruence.
              + my_update_destruct; try find_inversion; rewrite_update.
                * apply last_holder'_locked_extend.
                * erewrite locked_in_flight_all_clients_false in * by
                      eauto using locks_correct_locked_invariant, reachable_intro,
                                  locks_correct_invariant.
                  discriminate.
          }
        * { find_apply_lem_hyp ServerNetHandler_cases. break_and. subst.
            repeat split.
            - apply trace_mutex'_no_out_extend. auto.
            - intros. my_update_destruct; try discriminate.
              rewrite_update.
              find_apply_lem_hyp last_holder'_no_out_inv.
              auto.
            - intros. my_update_destruct; try discriminate; rewrite_update.
              apply last_holder'_no_out_extend. auto.
          }
      + unfold InputHandler in *. break_match.
        * unfold ClientIOHandler in *.
          { monad_unfold.
            repeat break_match; repeat find_inversion; intuition;
            repeat rewrite snoc_assoc in *;
            try apply trace_mutex'_no_out_extend;
            try find_apply_lem_hyp last_holder'_no_out_inv;
            try (apply last_holder'_no_out_extend; auto).
            - apply trace_mutual_exclusion'_extend_input; auto. congruence.
            - rewrite update_nop_ext.
              find_apply_lem_hyp last_holder'_input_inv; try congruence.
              auto.
            - match goal with
                | [ H : _ |- _ ] => rewrite update_nop in H
              end.
              apply last_holder'_input_extend; auto. congruence.
            - apply trace_mutex'_unlock_extend; auto.
            - rewrite last_holder_unlock_none in *; auto. discriminate.
            - my_update_destruct; try find_inversion; rewrite_update.
              + discriminate.
              + assert (mutual_exclusion (nwState st))
                       by eauto using mutual_exclusion_invariant, reachable_intro.
                unfold mutual_exclusion in *.
                assert (c = n) by eauto. congruence.
            - apply trace_mutex'_unlock_extend. auto.
            - rewrite update_nop.
              find_apply_lem_hyp last_holder_some_unlock_inv.
              auto.
            - match goal with
                | [ H : _ |- _ ] => rewrite update_nop in H
              end.
              assert (n <> c) by congruence.
              find_apply_hyp_hyp.
              apply last_holder'_neq_unlock_extend; auto.
            - apply trace_mutual_exclusion'_extend_input; auto. congruence.
            - rewrite update_nop_ext. find_apply_lem_hyp last_holder'_input_inv; try congruence.
              auto.
            - match goal with
                | [ H : _ |- _ ] => rewrite update_nop in H
              end.
              apply last_holder'_input_extend; auto. congruence.
          }
        * unfold ServerIOHandler in *.
          monad_unfold. find_inversion.
          { intuition;
            repeat rewrite snoc_assoc in *.
            - apply trace_mutex'_no_out_extend.
              apply trace_mutual_exclusion'_extend_input_server. auto.
            - find_apply_lem_hyp last_holder'_no_out_inv.
              rewrite update_nop. find_apply_lem_hyp last_holder'_input_inv_server. auto.
            - apply last_holder'_no_out_extend; auto.
              rewrite_update. unfold last_holder. rewrite last_holder'_server_extend.
              auto.
          }
  Qed.
End LockServ.
