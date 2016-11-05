Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Verdi.DynamicNet.
Require Import Verdi.Chord.
Require Coqlib.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Omega.

Set Bullet Behavior "Strict Subproofs".

Close Scope boolean_if_scope.
Open Scope general_if_scope.

Section ChordProof.
  Variable SUCC_LIST_LEN : nat.
  Variable N : nat.
  Variable hash : addr -> id.
  Variable hash_inj : forall a b : addr,
      hash a = hash b -> a = b.

  Notation start_handler := (start_handler SUCC_LIST_LEN hash).
  Notation recv_handler := (recv_handler SUCC_LIST_LEN hash).
  Notation timeout_handler := (timeout_handler hash).
  Notation tick_handler := (tick_handler hash).

  Notation handle_query_res := (handle_query_res SUCC_LIST_LEN hash).
  Notation handle_query_timeout := (handle_query_timeout hash).
  Notation send := (send addr payload).

  Notation global_state := (global_state addr payload data timeout).
  Notation nil_timeouts := (nil_timeouts addr timeout).
  Notation nodes := (nodes addr payload data timeout).
  Notation failed_nodes := (failed_nodes addr payload data timeout).
  Notation sigma := (sigma addr payload data timeout).
  Notation timeouts := (timeouts addr payload data timeout).
  Notation msgs := (msgs addr payload data timeout).
  Notation trace := (trace addr payload data timeout).
  Notation update_msgs := (update_msgs addr payload data timeout).
  Notation make_pointer := (make_pointer hash).

  Notation apply_handler_result := (apply_handler_result addr addr_eq_dec payload data timeout timeout_eq_dec).
  Notation end_query := (end_query hash).
  Notation start_query := (start_query hash).
  Notation handle_stabilize := (handle_stabilize SUCC_LIST_LEN hash).
  Notation try_rectify := (try_rectify hash).

  Notation msg := (msg addr payload).
  Notation event := (event addr payload timeout).
  Notation e_send := (e_send addr payload timeout).
  Notation e_recv := (e_recv addr payload timeout).
  Notation e_timeout := (e_timeout addr payload timeout).
  Notation e_fail := (e_fail addr payload timeout).

  Inductive between : id -> id -> id -> Prop :=
  | BetweenMono :
      forall a x b, a < b -> a < x -> x < b -> between a x b
  | BetweenWrapL :
      forall a x b, a >= b -> a < x -> between a x b
  | BetweenWrapR :
      forall a x b, a >= b -> x < b -> between a x b.

  Ltac inv_between :=
    match goal with
    | [H: between _ _ _ |- _] => inv H
    end.

  Lemma between_between_bool_equiv :
    forall a x b,
      between a x b <-> between_bool a x b = true.
  Proof.
    unfold between_bool.
    intros.
    split; intros.
    - inv_between;
        repeat break_if;
        omega || reflexivity.
    - repeat break_if;
        constructor;
        congruence || omega.
  Qed.

  Lemma between_bool_true_between :
    forall a x b,
      between_bool a x b = true ->
      between a x b.
  Proof.
    intros.
    now rewrite between_between_bool_equiv.
  Qed.

  Lemma between_bool_false_not_between :
    forall a x b,
      between_bool a x b = false ->
      ~ between a x b.
  Proof.
    intros.
    rewrite between_between_bool_equiv; congruence.
  Qed.

  Inductive request_response_pair : payload -> payload -> Prop :=
  | pair_GetBestPredecessor : forall n p, request_response_pair (GetBestPredecessor n) (GotBestPredecessor p)
  | pair_GetSuccList : forall l, request_response_pair GetSuccList (GotSuccList l)
  | pair_GetPredAndSuccs : forall p l, request_response_pair GetPredAndSuccs (GotPredAndSuccs p l)
  | pair_Ping : request_response_pair Ping Pong.

  Inductive timeout_constraint : global_state -> addr -> timeout -> Prop :=
  | Tick_unconstrained : forall gst h,
      timeout_constraint gst h Tick
  | KeepaliveTick_unconstrained : forall gst h,
      timeout_constraint gst h KeepaliveTick
  | Request_needs_dst_dead_and_no_msgs : forall gst dst h p,
      In dst (failed_nodes gst) ->
      (forall m, request_response_pair p m -> ~ In (dst, (h, m)) (msgs gst)) ->
      timeout_constraint gst h (Request dst p).

  Definition timeouts_detect_failure (gst : global_state) : Prop :=
    forall xs t ys h dead req,
      (trace gst) = xs ++ t :: ys ->
      (* if a request timeout occurs at some point in the trace... *)
      t = (e_timeout h (Request dead req)) ->
      (* then it corresponds to an earlier node failure. *)
      In (e_fail dead) xs.

  (* tip: treat this as opaque and use lemmas: it never gets stopped except by failure *)
  Definition live_node (gst : global_state) (h : addr) : Prop :=
    In h (nodes gst) /\
    ~ In h (failed_nodes gst) /\
    exists st,
      sigma gst h = Some st /\
      joined st = true.

  Definition dead_node (gst : global_state) (h : addr) : Prop :=
    In h (nodes gst) /\
    In h (failed_nodes gst) /\
    exists st,
      sigma gst h = Some st.

  Definition joining_node (gst : global_state) (h : addr) : Prop :=
    exists st,
      sigma gst h = Some st /\
      joined st = false /\
      In h (nodes gst) /\
      ~ In h (failed_nodes gst).

  Definition best_succ (gst : global_state) (h s : addr) : Prop :=
    exists st xs ys,
      live_node gst h /\
      sigma gst h = Some st /\
      map addr_of (succ_list st) = xs ++ s :: ys /\
      (forall o, In o xs -> dead_node gst o) /\
      live_node gst s.

  Definition live_node_in_succ_lists (gst : global_state) : Prop :=
    forall h st,
      sigma gst h = Some st ->
      live_node gst h ->
      exists s,
        best_succ gst h s.

  (* This is a way of dealing with succ lists missing entries
     mid-stabilization that doesn't involve putting artificial entries
     into the actual successor list. *)
  Definition ext_succ_list_span_includes (h : id) (succs : list id) (n : id) :=
    forall n l e,
      length (h :: succs) = n ->
      l = last succs h ->
      e = l + (SUCC_LIST_LEN - n) ->
      between h n e.

  (* "A principal node is a member that is not skipped by any member's
     extended successor list" *)
  Definition principal (gst : global_state) (p : addr) : Prop :=
    forall h st succs,
      live_node gst h ->
      sigma gst h = Some st ->
      map id_of (succ_list st) = succs ->
      ext_succ_list_span_includes h succs p ->
      In p succs.

  Definition principals (gst : global_state) (ps : list addr) : Prop :=
    NoDup ps /\
    Forall (principal gst) ps /\
    forall p, principal gst p -> In p ps.

  Definition sufficient_principals (gst : global_state) : Prop :=
    exists ps,
      principals gst ps /\
      length ps > SUCC_LIST_LEN.

  Definition principal_failure_constraint (gst : global_state) (f : addr) : Prop :=
    principal gst f ->
    forall ps,
      principals gst ps ->
      length ps > (SUCC_LIST_LEN + 1).

  Definition failure_constraint (gst : global_state) (f : addr) (gst' : global_state) : Prop :=
    live_node_in_succ_lists gst' /\
    principal_failure_constraint gst f.

  Notation step_dynamic := (step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec start_handler recv_handler timeout_handler timeout_constraint failure_constraint).

  Inductive request_payload : payload -> Prop :=
  | req_GetBestPredecessor : forall p, request_payload (GetBestPredecessor p)
  | req_GetSuccList : request_payload GetSuccList
  | req_GetPredAndSuccs : request_payload GetPredAndSuccs
  | req_Ping : request_payload Ping.

  Inductive response_payload : payload -> Prop :=
  | res_GotBestPredecessor : forall p, response_payload (GotBestPredecessor p)
  | res_GotSuccList : forall l, response_payload (GotSuccList l)
  | res_GotPredAndSuccs : forall p l, response_payload (GotPredAndSuccs p l)
  | res_Pong : response_payload Pong
  | res_Busy : response_payload Busy.

  Ltac request_payload_inversion :=
    match goal with
      | H : request_payload _ |- _ => inv H
    end.

  Lemma is_request_same_as_request_payload : forall msg : payload,
      is_request msg = true <-> request_payload msg.
  Proof.
    unfold is_request.
    intuition.
    - break_match;
        discriminate ||
        eauto using req_GetBestPredecessor, req_GetSuccList, req_GetPredAndSuccs, req_Ping.
    - now request_payload_inversion.
  Qed.

  Lemma busy_response_exists :
    forall msg st' sends nts cts src dst st,
      request_payload msg ->
      (st', sends, nts, cts) = handle_query_req_busy src dst st msg ->
      In (src, Busy) sends.
  Proof.
    unfold handle_query_req_busy.
    intuition.
    break_if;
    tuple_inversion;
    now apply in_eq.
  Qed.

  Lemma safe_msgs :
    forall msg,
      is_safe msg = true ->
      msg = Ping \/ msg = Notify.
  Proof.
    unfold is_safe.
    intuition.
    break_match; auto || discriminate.
  Qed.

  Lemma unsafe_msgs_not_safe_ones :
    forall msg,
      is_safe msg = false ->
      msg <> Notify /\ msg <> Ping.
  Proof.
    unfold is_safe.
    intuition;
      break_match;
      easy.
  Qed.

  Lemma only_safe_request_is_Ping :
    forall msg,
      request_payload msg ->
      is_safe msg = true ->
      msg = Ping.
  Proof.
    intuition.
    request_payload_inversion;
      find_apply_lem_hyp safe_msgs;
      break_or_hyp;
      auto || discriminate.
  Qed.

  Lemma handle_query_req_busy_sends_busy :
    forall src dst st msg st' ms nts cts,
      handle_query_req_busy src dst st msg = (st', ms, nts, cts) ->
      In (src, Busy) ms.
  Proof.
    unfold handle_query_req_busy.
    intuition.
    break_if;
    tuple_inversion;
    exact: in_eq.
  Qed.

  Lemma handle_query_req_gives_response :
    forall st m,
      is_safe m = false ->
      request_payload m ->
      exists p,
        handle_query_req st m = Some p.
  Proof.
    unfold handle_query_req.
    intuition.
    find_copy_apply_lem_hyp unsafe_msgs_not_safe_ones.
    break_and.
    request_payload_inversion;
      eauto || congruence.
  Qed.

  Lemma requests_are_always_responded_to : forall src dst msg st sends nts cts,
      request_payload msg ->
      (st, sends, nts, cts) = recv_handler src dst st msg ->
      exists res, In (src, res) sends.
  Proof.
    intuition.
    unfold recv_handler in *.
    find_copy_apply_lem_hyp is_request_same_as_request_payload.
    find_rewrite.
    break_match.
    - (* req is safe *)
      find_copy_apply_lem_hyp only_safe_request_is_Ping; auto.
      subst.
      simpl in *.
      tuple_inversion.
      eexists.
      exact: in_eq.
    - (* req is not safe *)
      break_match.
      * (* busy *)
        repeat break_let.
        exists Busy.
        eapply handle_query_req_busy_sends_busy; eauto.
      * (* not busy *)
        break_match.
        + tuple_inversion.
          eexists.
          exact: in_eq.
        + assert (exists p, handle_query_req st msg = Some p)
            by exact: handle_query_req_gives_response.
          break_exists.
          find_contradiction.
  Qed.

  Definition init_sigma (h : addr) : option data.
  Admitted. (* TODO should map base addresses to data for an ideal ring of just the base nodes *)
  Definition initial_st : global_state.
  Admitted.

  Inductive reachable_st : global_state -> Prop :=
    | reachableInit : reachable_st initial_st
    | reachableStep : forall gst gst',
        reachable_st gst ->
        step_dynamic gst gst' ->
        reachable_st gst'.

  Ltac induct_reachable_st :=
    match goal with
    | [H : reachable_st _ |- _ ] => prep_induction H; induction H
    end.

  Theorem live_node_characterization : forall gst h st,
      sigma gst h = Some st ->
      joined st = true ->
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      live_node gst h.
  Proof.
    unfold live_node.
    intuition.
    match goal with
      | x : data |- exists _ : data, _ => exists x
    end.
    intuition.
  Qed.

  Definition live_node_bool (gst : global_state) (h : addr) :=
    match sigma gst h with
      | Some st => if joined st
                   then if in_dec addr_eq_dec h (nodes gst)
                        then if in_dec addr_eq_dec h (failed_nodes gst)
                             then false
                             else true
                        else false
                   else false
      | None => false
    end.

  Ltac break_step :=
    match goal with
      | H : step_dynamic _ _ |- _ =>
        induction H
    end; subst.

  Ltac break_live_node :=
    match goal with
      | H : live_node _ _ |- _ =>
        unfold live_node in H; repeat break_and; break_exists; repeat break_and
    end.

  Ltac break_live_node_name var :=
    match goal with
      | H : live_node _ _ |- _ =>
        unfold live_node in H; repeat break_and; break_exists_name var; repeat break_and
    end.

  Ltac break_live_node_exists_exists :=
    match goal with
      | H : live_node _ _ |- _ =>
        unfold live_node in H; repeat break_and; break_exists_exists; repeat break_and
    end.

  Ltac break_dead_node :=
    match goal with
      | H : dead_node _ _ |- _ =>
        unfold dead_node in H; repeat break_and; break_exists; repeat break_and
    end.

  Ltac break_dead_node_name var :=
    match goal with
      | H : dead_node _ _ |- _ =>
        unfold dead_node in H; repeat break_and; break_exists_name var; repeat break_and
    end.

  Ltac break_dead_node_exists_exists :=
    match goal with
      | H : dead_node _ _ |- _ =>
        unfold dead_node in H; repeat break_and; break_exists_exists; repeat break_and
    end.

  Definition live_node_dec (gst : global_state) :
    forall h,
      {live_node gst h} + {~ live_node gst h}.
  Proof.
    move => h.
    destruct (sigma gst h) as [st |] eqn:H_st.
    - destruct (joined st) eqn:H_joined;
        destruct (In_dec addr_eq_dec h (nodes gst));
        destruct (In_dec addr_eq_dec h (failed_nodes gst));
        try (right; move => H_live; break_live_node; easy || congruence).
      left; eapply live_node_characterization; eauto.
    - right.
      move => H_live.
      break_live_node.
      congruence.
  Defined.

  Theorem live_node_dec_equiv_live_node : forall gst h,
      live_node gst h <-> live_node_bool gst h = true.
  Proof.
    unfold live_node_bool.
    intuition.
    - repeat break_match;
        break_live_node;
        congruence || auto.
    - repeat break_match;
        congruence || eauto using live_node_characterization.
  Qed.

  (* transitive closure of best_succ *)
  (* treat as opaque *)
  Inductive reachable (gst : global_state) : addr -> addr -> Prop :=
    | ReachableSucc : forall from to,
        best_succ gst from to ->
        reachable gst from to
    | ReachableTransL : forall from x to,
        best_succ gst from x ->
        reachable gst x to ->
        reachable gst from to.

  Ltac induct_reachable :=
    match goal with
      | H : reachable _ _ _ |- _ =>
        induction H
    end.

  Lemma ReachableTransR : forall gst from x to,
      reachable gst from x ->
      best_succ gst x to ->
      reachable gst from to.
  Proof.
    intuition.
    induct_reachable.
    - eapply ReachableTransL.
      eauto.
      eapply ReachableSucc.
      eauto.
    - eauto using ReachableTransL.
  Qed.

  Lemma ReachableTrans : forall gst from x to,
      reachable gst from x ->
      reachable gst x to ->
      reachable gst from to.
  Proof.
    intros gst from x to H.
    generalize dependent to.
    induction H.
    - intuition.
      eauto using ReachableSucc, ReachableTransL.
    - intuition.
      eauto using ReachableSucc, ReachableTransL.
  Qed.

  Definition best_succ_of (gst : global_state) (h : addr) : option addr :=
    match (sigma gst) h with
      | Some st => head (filter (live_node_bool gst) (map addr_of (succ_list st)))
      | None => None
    end.

  (* treat as opaque *)
  Definition ring_member (gst : global_state) (h : addr) : Prop :=
    reachable gst h h.
  Hint Unfold ring_member.

  Definition at_least_one_ring (gst : global_state) : Prop :=
    exists h, ring_member gst h.

  Definition at_most_one_ring (gst : global_state) : Prop :=
    forall x y,
      ring_member gst x ->
      ring_member gst y ->
      reachable gst x y.

  Definition ordered_ring (gst : global_state) : Prop :=
    forall h s x,
      ring_member gst h ->
      best_succ gst h s ->
      ring_member gst x ->
      ~ between h x s.
      (* or between h x s -> s = x *)

  Definition connected_appendages (gst : global_state) : Prop :=
    forall a, live_node gst a ->
      exists r, ring_member gst r /\ reachable gst a r.

  Definition state_invariant (gst : global_state) : Prop :=
    sufficient_principals gst /\
    live_node_in_succ_lists gst.

  (* this is not quite what it sounds like, since Chord.start_query will sometimes not send anything *)
  Inductive query_request : query -> payload -> Prop :=
    | QReq_RectifyPing : forall n, query_request (Rectify n) Ping
    | QReq_StabilizeGetPredAndSuccs : query_request Stabilize GetPredAndSuccs
    | QReq_Stabilize2 : forall p, query_request (Stabilize2 p) GetSuccList
    | QReq_JoinGetBestPredecessor : forall k a, query_request (Join k) (GetBestPredecessor a)
    | QReq_JoinGetSuccList : forall k, query_request (Join k) GetSuccList
    | QReq_Join2 : forall n, query_request (Join2 n) GetSuccList.

  Inductive query_response : query -> payload -> Prop :=
    | QRes_RectifyPong : forall n, query_response (Rectify n) Pong
    | QRes_StabilizeGetPredAndSuccs : forall p l, query_response Stabilize (GotPredAndSuccs p l)
    | QRes_Stabilize2 : forall p l, query_response (Stabilize2 p) (GotSuccList l)
    | QRes_JoinGotBestPredecessor : forall k p, query_response (Join k) (GotBestPredecessor p)
    | QRes_JoinGotSuccList : forall k l, query_response (Join k) (GotSuccList l)
    | QRes_Join2 : forall n l, query_response (Join2 n) (GotSuccList l).

  (* for all nodes, query = none -> no request or response in the network for node *)
  (* for all nodes, query = some -> exactly one corresponding req or res in net *)
  Definition request_for_query (gst : global_state) (src dst : addr) (q : query) (msg : payload) : Prop :=
      query_request q msg /\
      In (src, (dst, msg)) (msgs gst).

  Definition response_for_query (gst : global_state) (src dst : addr) (q : query) (msg : payload) : Prop :=
      query_response q msg /\
      In (dst, (src, msg)) (msgs gst).

  Definition query_delayed_at (dst : addr) (st : data) (src : addr) (msg : payload) : Prop :=
    In (src, msg) (delayed_queries st).

  Definition addr_eqb : addr -> addr -> bool :=
    Nat.eqb.

  Lemma addr_eqb_true :
    forall a b,
      addr_eqb a b = true ->
      a = b.
  Proof.
    exact beq_nat_true.
  Qed.

  Lemma addr_eqb_false :
    forall a b,
      addr_eqb a b = false ->
      a <> b.
  Proof.
    exact beq_nat_false.
  Qed.

  Lemma addr_eqb_refl :
    forall a,
      addr_eqb a a = true.
  Proof.
    symmetry.
    apply beq_nat_refl.
  Qed.

  Definition on_channel (src dst : addr) (t : addr * (addr * payload)) :=
    let '(s, (d, m)) := t in
    andb (addr_eqb src s) (addr_eqb dst d).

  Definition channel (gst : global_state) (src dst : addr) : list payload :=
    filterMap
      (fun m =>
         if andb (addr_eqb (fst m) src)
                 (addr_eqb (fst (snd m)) dst)
         then Some (snd (snd m))
         else None)
      (msgs gst).

  (* note: this doesn't really tell you anything about repeated messages *)
  Lemma channel_contents :
    forall gst src dst p,
        In (src, (dst, p)) (msgs gst) <-> In p (channel gst src dst).
  Proof.
    unfold channel.
    intuition.
    - eapply filterMap_In; eauto.
      now repeat rewrite addr_eqb_refl.
    - find_eapply_lem_hyp In_filterMap; eauto.
      break_exists.
      break_and.
      assert (x = (src, (dst, p))).
      { break_if; try discriminate.
        find_apply_lem_hyp Bool.andb_true_iff; break_and.
        repeat find_apply_lem_hyp addr_eqb_true.
        find_injection.
        now repeat apply injective_projections. }
      now find_reverse_rewrite.
  Qed.

  (* If we have an open query at a live node, we have one of the following:
     - an appropriate request from src to dst
       and no other requests from src to dst
       and no responses from dst to src
       and no pending queries from src in the local state of dst
     - an appropriate response from dst to src
       and no requests from src to dst
       and no other responses from dst to src
       and no pending queries from src in the local state of dst
     - a corresponding pending query from src in the local state of dst
       and no requests from src to dst
       and no responses from dst to src *)
  Definition request_in_transit (gst : global_state) (src dst : addr) (q : query) : Prop :=
    forall chan,
      chan = channel gst src dst ->
      exists req,
        query_request q req /\
        In req chan /\
        (* no other requests *)
        (forall m xs ys,
            chan = xs ++ req :: ys ->
            In m (xs ++ ys) ->
            request_payload m ->
            m = req) /\
        (* no responses *)
        (forall m,
            In m (channel gst dst src) ->
            ~ response_payload m) /\
        (forall m st,
            sigma gst dst = Some st ->
            ~ query_delayed_at dst st src m).

  Definition response_in_transit (gst : global_state) (src dst : addr) (q : query) : Prop :=
    forall chan,
      chan = channel gst dst src ->
      exists res,
        query_response q res /\
        In res chan /\
        (* no other responses *)
        (forall m xs ys,
            chan = xs ++ res :: ys ->
            In m (xs ++ ys) ->
            response_payload m ->
            m = res) /\
        (* no requests *)
        (forall m,
            In m (channel gst src dst) ->
            ~ request_payload m) /\
        (forall m st,
            sigma gst dst = Some st ->
            ~ query_delayed_at dst st src m).

  Definition pending_query (gst : global_state) (src dst : addr) (q : query) : Prop :=
    (forall st,
        exists m,
          sigma gst src = Some st ->
          query_delayed_at dst st src m) /\
    (forall m,
        In m (channel gst src dst) ->
        ~ request_payload m) /\
    (forall m,
        In m (channel gst dst src) ->
        ~ response_payload m).

  Theorem queries_always_remote :
    forall gst,
      reachable_st gst ->
      forall h st dstp q p,
        sigma gst h = Some st ->
        cur_request st = Some (dstp, q, p) ->
        h <> (addr_of dstp).
  Admitted.

  Definition query_state_net_invariant (gst : global_state) : Prop :=
    forall src st dstp q m,
      In src (nodes gst) ->
      sigma gst src = Some st ->
      cur_request st = Some (dstp, q, m) ->
      src <> (addr_of dstp) /\
      (request_in_transit gst src (addr_of dstp) q \/
       response_in_transit gst src (addr_of dstp) q \/
       pending_query gst src (addr_of dstp) q).

  Lemma query_state_net_invariant_elim :
    forall gst,
      query_state_net_invariant gst ->
      forall src dstp q st m,
        In src (nodes gst) ->
        sigma gst src = Some st ->
        cur_request st = Some (dstp, q, m) ->
        src <> (addr_of dstp) /\
        (request_in_transit gst src (addr_of dstp) q \/
         response_in_transit gst src (addr_of dstp) q \/
         pending_query gst src (addr_of dstp) q).
  Proof.
    eauto.
  Qed.

  Definition query_set_for_request (st : data) (dst : addr) (r : payload) :=
    exists q remove,
      cur_request st = Some (make_pointer dst, q, remove) /\
      query_request q r.

  Definition request_timed_out (gst : global_state) (src dst : addr) (r : payload) :=
    forall req_event,
      req_event = e_send (dst, (src, r)) ->
      exists before since,
        trace gst = before ++ req_event :: since /\
        ~ In req_event since /\
        In (e_timeout src (Request dst r)) since.

  Definition requests_have_queries_or_timeouts (gst : global_state) : Prop :=
    forall src dst r st,
      request_payload r ->
      In (dst, (src, r)) (msgs gst) ->
      sigma gst src = Some st ->
      query_set_for_request st dst r \/ request_timed_out gst src dst r.

  Definition timeouts_match_msg (gst : global_state) : Prop :=
    forall src dst m,
      In (Request dst m) (timeouts gst src) ->
      In src (nodes gst) ->
      In (src, (dst, m)) (msgs gst) \/
      exists p,
        request_response_pair m p /\
        In (dst, (src, p)) (msgs gst).

  Definition timeouts_match_query (gst : global_state) : Prop :=
    forall src dst st m p,
      In (Request dst m) (timeouts gst src) ->
      In src (nodes gst) ->
      sigma gst src = Some st ->
      addr_of p = dst ->
      exists q,
        cur_request st = Some (p, q, m) /\
        query_request q m.

  Definition responses_have_queries (gst : global_state) : Prop :=
    forall src dst r st,
      sigma gst src = Some st ->
      response_payload r ->
      In (src, (dst, r)) (msgs gst) ->
      exists q m,
        query_request q r /\
        cur_request st = Some (make_pointer dst, q, m).

  (* should follow from invariant *)
  Definition Request_goes_to_real_node (gst : global_state) : Prop :=
    forall src dst p,
      In (Request dst p) (timeouts gst src) ->
      In dst (nodes gst).

  Definition network_invariant (gst : global_state) : Prop :=
    True.

  Definition live_nodes_have_state (gst : global_state) : Prop :=
    forall h,
      In h (nodes gst) ->
      exists st,
        sigma gst h = Some st.

  Theorem nodes_have_state :
    forall gst gst',
      live_nodes_have_state gst ->
      step_dynamic gst gst' ->
      live_nodes_have_state gst'.
  Proof.
    unfold live_nodes_have_state.
    move => gst gst' H_st H_step n H_in.
    break_step.
    - destruct (addr_eq_dec h n).
      + subst_max.
        apply update_for_start_sigma_h_exists.
      + find_rewrite_lem update_for_start_nodes_eq.
        find_apply_lem_hyp in_inv.
        break_or_hyp; try (exfalso; eauto; fail).
        find_apply_lem_hyp H_st.
        break_exists_exists.
        eapply update_for_start_sigma_h_n; eauto.
    - eauto.
    - destruct (addr_eq_dec h n).
      * eexists.
        now apply update_eq.
      * find_apply_lem_hyp H_st.
        break_exists_exists.
        find_reverse_rewrite.
        now apply update_diff.
    - (*simpl in *.*)
      destruct (addr_eq_dec (fst (snd m)) n).
      * eexists.
        now apply update_eq.
      * simpl.
        find_apply_lem_hyp H_st.
        break_exists_exists.
        repeat find_reverse_rewrite.
        now apply update_diff.
  Qed.

  Theorem network_invariant_is_inductive :
    forall gst gst',
      network_invariant gst ->
      step_dynamic gst gst' ->
      network_invariant gst'.
  Abort.

  Definition inductive_invariant (gst : global_state) : Prop :=
    state_invariant gst /\
    network_invariant gst.

  Ltac break_invariant :=
    match goal with
      | H : inductive_invariant _ |- _ =>
        unfold inductive_invariant, state_invariant, network_invariant in H; break_and
    end.

  Lemma live_node_specificity : forall gst gst',
      nodes gst = nodes gst' ->
      failed_nodes gst = failed_nodes gst' ->
      sigma gst = sigma gst' ->
      live_node gst = live_node gst'.
  Proof.
    intuition.
    unfold live_node.
    repeat find_rewrite.
    auto.
  Qed.

  Lemma live_node_joined : forall gst h,
      live_node gst h ->
      exists st,
        sigma gst h = Some st /\
        joined st = true.
  Proof.
    intuition.
    by break_live_node_exists_exists.
  Qed.

  Lemma live_node_in_nodes : forall gst h,
      live_node gst h ->
      In h (nodes gst).
  Proof.
    intuition.
    by break_live_node.
  Qed.

  Lemma live_node_not_in_failed_nodes : forall gst h,
      live_node gst h ->
      ~ In h (failed_nodes gst).
  Proof.
    intuition.
    by break_live_node.
  Qed.

  Lemma live_node_equivalence : forall gst gst' h st st',
      live_node gst h ->
      nodes gst = nodes gst' ->
      failed_nodes gst = failed_nodes gst' ->
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      joined st = joined st' ->
      live_node gst' h.
  Proof.
    intuition.
    break_live_node.
    eapply live_node_characterization.
    * eauto.
    * repeat find_rewrite.
      find_injection.
      eauto.
    * repeat find_rewrite; auto.
    * repeat find_rewrite; auto.
  Qed.

  Lemma live_node_means_state_exists : forall gst h,
      live_node gst h ->
      exists st, sigma gst h = Some st.
  Proof.
    intuition.
    find_apply_lem_hyp live_node_joined.
    break_exists_exists.
    by break_and.
  Qed.

  Lemma coarse_live_node_characterization : forall gst gst' h,
      live_node gst h ->
      nodes gst = nodes gst' ->
      failed_nodes gst = failed_nodes gst' ->
      sigma gst = sigma gst' ->
      live_node gst' h.
  Proof.
    intuition.
    find_copy_apply_lem_hyp live_node_means_state_exists.
    break_exists.
    eapply live_node_equivalence.
    * repeat find_rewrite; eauto.
    * repeat find_rewrite; eauto.
    * repeat find_rewrite; eauto.
    * repeat find_rewrite; eauto.
    * repeat find_rewrite; eauto.
    * repeat find_rewrite; eauto.
  Qed.

  Lemma apply_handler_result_preserves_nodes : forall gst gst' h res e,
      gst' = apply_handler_result h res e gst ->
      nodes gst = nodes gst'.
  Proof.
    unfold apply_handler_result.
    intuition.
    repeat break_let.
    find_rewrite; auto.
  Qed.

  Lemma apply_handler_result_preserves_failed_nodes : forall gst gst' h res e,
      gst' = apply_handler_result h res e gst ->
      failed_nodes gst = failed_nodes gst'.
  Proof.
    unfold apply_handler_result.
    intuition.
    repeat break_let.
    find_rewrite; auto.
  Qed.

  Lemma when_apply_handler_result_preserves_live_node :
    forall h h0 st st' gst gst' e ms cts nts,
      live_node gst h ->
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      joined st' = true ->
      gst' = apply_handler_result h0 (st', ms, cts, nts) e gst ->
      live_node gst' h.
  Proof.
    intuition.
    eapply live_node_characterization.
    - eauto.
    - break_live_node.
      repeat find_rewrite.
      find_inversion; eauto.
    - find_apply_lem_hyp apply_handler_result_preserves_nodes.
      find_inversion.
      break_live_node; auto.
    - find_apply_lem_hyp apply_handler_result_preserves_failed_nodes.
      find_inversion.
      break_live_node; auto.
  Qed.

  Lemma joined_preserved_by_start_query : forall h st k st' ms nts cts,
      start_query h st k = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold start_query.
    intuition.
    break_match.
    - break_let.
      tuple_inversion.
      unfold update_query; auto.
    - tuple_inversion; auto.
  Qed.

  Lemma joined_preserved_by_try_rectify : forall h st st' ms ms' cts cts' nts nts',
      try_rectify h (st, ms, cts, nts) = (st', ms', cts', nts') ->
      joined st = joined st'.
  Proof.
    unfold try_rectify, clear_rectify_with.
    simpl.
    intuition.
    repeat break_match.
    - find_inversion.
      find_apply_lem_hyp joined_preserved_by_start_query; auto.
    - find_inversion; auto.
    - find_inversion; auto.
    - find_inversion; auto.
  Qed.

  Lemma joined_preserved_by_handle_delayed_queries :
    forall h st st' ms nts cts,
      handle_delayed_queries h st = (st', ms, nts, cts) ->
      joined st = joined st'.
  Admitted.

  Lemma joined_preserved_by_end_query : forall h st st' ms ms' cts cts' nts nts',
      end_query h (st, ms, cts, nts) = (st', ms', cts', nts') ->
      joined st = joined st'.
  Proof.
    unfold end_query.
    intuition.
    repeat break_let.
    find_apply_lem_hyp joined_preserved_by_try_rectify.
    find_apply_lem_hyp joined_preserved_by_handle_delayed_queries.
    simpl in *. (* simpl-ing through clear_query *)
    now find_rewrite.
  Qed.

  Lemma joined_preserved_by_handle_stabilize : forall h src st q new_succ succ st' ms nts cts,
      handle_stabilize h src st q new_succ succ = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold handle_stabilize.
    unfold update_succ_list.
    intuition.
    repeat break_match.
    - find_apply_lem_hyp joined_preserved_by_start_query; auto.
    - find_apply_lem_hyp joined_preserved_by_end_query; auto.
  Qed.

  Lemma joined_preserved_by_end_query_handle_rectify : forall h st p n st' ms nts cts,
      end_query h (handle_rectify st p n) = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold handle_rectify.
    intuition.
    repeat break_match;
      find_apply_lem_hyp joined_preserved_by_end_query;
      now simpl in *.
  Qed.

  (* not as strong as the other ones since handle_query for a Join query can change joined st from false to true *)
  Lemma joined_preserved_by_handle_query : forall src h st p q m st' ms nts cts,
        handle_query_res src h st p q m = (st', ms, nts, cts) ->
        joined st = true ->
        joined st' = true.
  Admitted.

  Lemma joined_preserved_by_recv_handler : forall src h st msg st' ms nts cts,
      recv_handler src h st msg = (st', ms, nts, cts) ->
      joined st = true ->
      joined st' = true.
  Proof.
    unfold recv_handler.
    intuition.
  Admitted.

  Lemma joined_preserved_by_tick_handler : forall h st st' ms nts cts,
    tick_handler h st = (st', ms, nts, cts) ->
    joined st = joined st'.
  Proof.
    unfold tick_handler, add_tick.
    intuition.
    - repeat break_match; repeat tuple_inversion; auto.
      * repeat tuple_inversion.
        find_apply_lem_hyp joined_preserved_by_start_query; eauto.
  Qed.

  Lemma joined_preserved_by_update_pred : forall st p st',
      st' = update_pred st p ->
      joined st = joined st'.
  Proof.
    unfold update_pred.
    intuition.
    find_rewrite; auto.
  Qed.

  Lemma joined_preserved_by_handle_query_timeout : forall h st dst q st' ms nts cts,
      handle_query_timeout h st dst q = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold handle_query_timeout.
    intuition.
    repeat break_match;
      find_apply_lem_hyp joined_preserved_by_end_query ||
      find_apply_lem_hyp joined_preserved_by_start_query;
      eauto.
  Qed.

  Lemma joined_preserved_by_timeout_handler : forall h st t st' ms nts cts,
    timeout_handler h st t = (st', ms, nts, cts) ->
    joined st = joined st'.
  Proof.
    unfold timeout_handler.
    intuition.
    repeat break_match;
      try tuple_inversion;
      eauto using joined_preserved_by_tick_handler, joined_preserved_by_handle_query_timeout.
  Qed.

  Lemma update_determined_by_f : forall A (f : addr -> A) x d d' y,
    y <> x ->
    update addr_eq_dec f x d y = d' ->
    f y = d'.
  Proof.
    intuition.
    symmetry.
    repeat find_reverse_rewrite.
    apply update_diff.
    now apply not_eq_sym.
  Qed.

  Lemma apply_handler_result_updates_sigma : forall h st ms nts cts e gst gst',
      gst' = apply_handler_result h (st, ms, nts, cts) e gst ->
      sigma gst' h = Some st.
  Proof.
    unfold apply_handler_result, update.
    intuition.
    repeat find_rewrite.
    simpl in *.
    break_if; congruence.
  Qed.

  Lemma apply_handler_result_In_timeouts :
    forall t h0 h st ms nts cts e gst,
      In t (timeouts (apply_handler_result h0 (st, ms, nts, cts) e gst) h) ->
      In t nts \/
      In t (timeouts gst h) /\ (~ In t cts \/ h <> h0).
  Admitted.

  Theorem live_node_preserved_by_recv_step : forall gst h src st msg gst' e st' ms nts cts,
      live_node gst h ->
      Some st = sigma gst h ->
      recv_handler src h st msg = (st', ms, nts, cts) ->
      gst' = apply_handler_result h (st', ms, nts, cts) e gst ->
      live_node gst' h.
  Proof.
    intuition.
    eapply when_apply_handler_result_preserves_live_node; eauto.
    - eauto using apply_handler_result_updates_sigma.
    - eapply joined_preserved_by_recv_handler.
      * eauto.
      * break_live_node.
        find_rewrite.
        find_injection.
        auto.
  Qed.

  Theorem live_node_preserved_by_timeout_step : forall gst h st st' t ms nts cts e gst',
      live_node gst h ->
      sigma gst h = Some st ->
      timeout_handler h st t = (st', ms, nts, cts) ->
      gst' = apply_handler_result h (st', ms, nts, t :: cts) e gst ->
      live_node gst' h.
  Proof.
    intuition.
    eapply when_apply_handler_result_preserves_live_node; eauto.
    - eauto using apply_handler_result_updates_sigma.
    - break_live_node.
      find_apply_lem_hyp joined_preserved_by_timeout_handler.
      repeat find_rewrite.
      find_injection.
      eauto.
  Qed.

  Lemma adding_nodes_does_not_affect_live_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      live_node gst h ->
      live_node gst' h.
  Proof.
    intuition.
    break_live_node_name d.
    repeat split.
    * repeat find_rewrite.
      now apply in_cons.
    * by find_rewrite.
    * exists d.
      split => //.
      repeat find_reverse_rewrite.
      find_rewrite.
      find_rewrite.
      apply update_diff.
      congruence.
  Qed.

  (* reverse of the above, with additional hypothesis that h <> n. *)
  Lemma adding_nodes_did_not_affect_live_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      sigma gst' = update addr_eq_dec (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      live_node gst' h ->
      h <> n ->
      live_node gst h.
  Proof.
    intuition.
    unfold live_node.
    break_live_node_name d.
    repeat split.
    * repeat find_rewrite.
      find_apply_lem_hyp in_inv.
      break_or_hyp; congruence.
    * repeat find_rewrite.
      auto.
    * exists d.
      split => //.
      repeat find_reverse_rewrite.
      find_rewrite.
      find_rewrite.
      find_rewrite.
      find_rewrite.
      symmetry.
      apply update_diff; auto.
  Qed.

  Lemma adding_nodes_does_not_affect_dead_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      sigma gst' = update addr_eq_dec (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      dead_node gst h ->
      dead_node gst' h.
  Proof.
    intuition.
    break_dead_node_name d.
    repeat split.
    - find_rewrite.
      eauto using in_cons.
    - find_rewrite; auto.
    - exists d.
      repeat find_reverse_rewrite.
      find_rewrite.
      find_rewrite.
      eapply update_diff.
      congruence.
  Qed.

  Lemma adding_nodes_did_not_affect_dead_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      In h (nodes gst) ->
      sigma gst' = update addr_eq_dec (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      dead_node gst' h ->
      dead_node gst h.
  Proof.
    intuition.
    break_dead_node_name d.
    unfold dead_node.
    repeat split.
    - find_rewrite.
      eauto using in_cons.
    - now repeat find_rewrite.
    - eexists.
      eapply update_determined_by_f.
      * instantiate (1 := n).
        eauto using In_notIn_implies_neq.
      * repeat find_rewrite; eauto.
  Qed.

  Lemma coarse_dead_node_characterization : forall gst gst' h,
      dead_node gst h ->
      sigma gst' = sigma gst ->
      nodes gst' = nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      dead_node gst' h.
  Proof.
    intuition.
    break_dead_node_name d.
    repeat split; try (find_rewrite; auto).
    now exists d.
  Qed.

  Lemma coarse_best_succ_characterization : forall gst gst' h s,
      best_succ gst h s ->
      sigma gst' = sigma gst ->
      nodes gst' = nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      best_succ gst' h s.
  Proof.
    unfold best_succ in *.
    intuition.
    break_exists_exists.
    break_and.
    repeat break_and_goal.
    - eapply live_node_equivalence; eauto.
      now repeat find_rewrite.
    - now repeat find_rewrite.
    - easy.
    - move => o H_in.
      find_apply_hyp_hyp.
      eapply coarse_dead_node_characterization; eauto.
    - eapply coarse_live_node_characterization; eauto.
  Qed.

  Lemma adding_nodes_does_not_affect_best_succ : forall gst gst' h s n st,
      best_succ gst h s ->
      ~ In n (nodes gst) ->
      sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      best_succ gst' h s.
  Proof.
    unfold best_succ.
    intuition.
    break_exists_exists.
    break_and.
    repeat break_and_goal;
      eauto using adding_nodes_does_not_affect_live_node.
    - repeat break_live_node.
      repeat find_rewrite.
      match goal with
      | H: sigma gst h = Some _ |- _ = Some _ => rewrite <- H
      end.
      eapply update_diff.
      congruence.
    - intuition.
      find_copy_apply_hyp_hyp.
      break_dead_node.
      eauto using adding_nodes_does_not_affect_dead_node.
  Qed.

  Lemma in_half_means_in_whole : forall A (x : A) (xs ys : list A),
      In x xs -> In x (xs ++ ys).
  Proof.
    intuition.
  Qed.

  Lemma in_middle_means_in_whole : forall A (x : A) (xs ys : list A),
      In x (xs ++ x :: ys).
  Proof.
    intuition.
  Qed.

  Lemma adding_nodes_did_not_affect_best_succ : forall gst gst' h s n st,
      best_succ gst' h s ->
      In h (nodes gst) ->
      ~ In n (nodes gst) ->
      sigma gst' h = Some st ->
      ~ In n (map addr_of (succ_list st)) ->
      sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      best_succ gst h s.
  Proof.
    intuition.
    unfold best_succ in *.
    break_exists_exists.
    break_and.
    repeat break_and_goal.
    - break_live_node.
      break_live_node.
      unfold live_node.
      repeat find_rewrite.
      repeat break_and_goal; eauto.
      eexists; split; eauto.
  Admitted.
 (*

      break_exists.
      break_and.
      match goal with
        | H : sigma gst' ?h = Some ?st |- exists _, sigma gst ?h = _ /\ _ => exists st
      end.
      repeat find_rewrite.
      repeat find_injection.
      repeat split.
      * match goal with
        | H: sigma _ = update _ _ _ (Some ?st) |- sigma _ _ = Some ?st => symmetry in H
        end.
        eapply update_determined_by_f.
        + eapply In_notIn_implies_neq; eauto.
        + eauto.
      * eauto.
      * eauto.
      * eauto.
    - repeat find_reverse_rewrite.
      eapply update_determined_by_f;
        [eapply In_notIn_implies_neq; now eauto|]; now repeat find_rewrite.
    - eauto.
    - intuition.
      eapply adding_nodes_did_not_affect_dead_node; eauto.
      find_copy_apply_hyp_hyp.
      unfold dead_node in *.
      break_exists.
      break_and.
      repeat find_rewrite.
      find_injection.
      eapply In_cons_neq.
      * eauto.
      * intuition; subst.
        find_false.
        repeat find_rewrite.
        auto using in_half_means_in_whole.
    - eapply adding_nodes_did_not_affect_live_node; eauto.
      * intuition; subst.
        find_false.
        repeat (find_rewrite; try find_injection).
        auto using in_middle_means_in_whole.
  Qed.
*)
  Lemma coarse_reachable_characterization : forall from to gst gst',
      reachable gst from to ->
      nodes gst' = nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      sigma gst' = sigma gst ->
      reachable gst' from to.
  Proof.
    intuition.
    induction H;
      eauto using ReachableSucc, ReachableTransL, coarse_best_succ_characterization.
  Qed.

  Lemma adding_node_preserves_reachable : forall h from to gst gst' st,
        reachable gst from to ->
        ~ In h (nodes gst) ->
        nodes gst' = h :: nodes gst ->
        failed_nodes gst' = failed_nodes gst ->
        sigma gst' = update addr_eq_dec (sigma gst) h (Some st) ->
        reachable gst' from to.
  Proof.
    intuition.
    induction H;
      eauto using ReachableSucc, ReachableTransL, adding_nodes_does_not_affect_best_succ.
  Qed.

  Ltac break_best_succ :=
    match goal with
      | H : best_succ _ _ _ |- _ =>
        let x := fresh in
        pose proof H as x;
        unfold best_succ in x;
        break_exists;
        break_and
    end.

  Lemma adding_node_preserves_reachable_converse : forall h from to gst gst' st,
        reachable gst' from to ->
        ~ In h (nodes gst) ->
        In from (nodes gst) ->
        nodes gst' = h :: nodes gst ->
        failed_nodes gst' = failed_nodes gst ->
        sigma gst' = update addr_eq_dec (sigma gst) h st ->
        reachable gst from to.
  Admitted.

  Definition fail_step_preserves (P : global_state -> Prop) : Prop :=
    forall gst gst' h,
      inductive_invariant gst ->
      In h (nodes gst) ->
      sigma gst' = sigma gst ->
      nodes gst' = nodes gst ->
      failed_nodes gst' = h :: failed_nodes gst ->
      P gst'.

  Definition timeout_step_preserves (P : global_state -> Prop) : Prop :=
    forall gst gst' h st t st' ms newts clearedts,
      inductive_invariant gst ->
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = Some st ->
      In t (timeouts gst h) ->
      timeout_handler h st t = (st', ms, newts, clearedts) ->
      gst' = (apply_handler_result
               h
               (st', ms, newts, t :: clearedts)
               (e_timeout h t)
               gst) ->
      P gst'.

  Definition preserved_when_nodes_and_sigma_preserved (P : global_state -> Prop) : Prop :=
      forall gst gst',
          inductive_invariant gst ->
          nodes gst' = nodes gst ->
          failed_nodes gst' = failed_nodes gst ->
          sigma gst' = sigma gst ->
          P gst'.

  Definition node_deliver_step_preserves (P : global_state -> Prop) : Prop :=
    forall gst xs m ys gst' h d st ms nts cts e,
      inductive_invariant gst ->
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = Some d ->
      h = fst (snd m) ->
      msgs gst = xs ++ m :: ys ->
      gst' = update_msgs gst (xs ++ ys) ->
      recv_handler (fst m) h d (snd (snd m)) = (st, ms, nts, cts) ->
      P (apply_handler_result h (st, ms, nts, cts) e gst').

  (** Valid pointers *)
  Definition valid_ptr (gst : global_state) (p : pointer) : Prop :=
    id_of p = hash (addr_of p) /\
    In (addr_of p) (nodes gst).

  Lemma valid_ptr_intro :
    forall gst p,
      id_of p = hash (addr_of p) ->
      In (addr_of p) (nodes gst) ->
      valid_ptr gst p.
  Proof.
    easy.
  Qed.

  Lemma valid_ptr_elim :
    forall gst p,
      valid_ptr gst p ->
      id_of p = hash (addr_of p) /\
      In (addr_of p) (nodes gst).
  Proof.
    unfold valid_ptr.
    easy.
  Qed.

  Lemma valid_ptr_elim_hash :
    forall gst p,
      valid_ptr gst p ->
      id_of p = hash (addr_of p).
  Proof.
    unfold valid_ptr.
    easy.
  Qed.

  Lemma valid_ptr_elim_nodes :
    forall gst p,
      valid_ptr gst p ->
      In (addr_of p) (nodes gst).
  Proof.
    unfold valid_ptr.
    easy.
  Qed.

  Lemma valid_ptr_nodes_subset :
    forall gst gst' p,
      valid_ptr gst p ->
      (forall n, In n (nodes gst) -> In n (nodes gst')) ->
      valid_ptr gst' p.
  Proof.
    unfold valid_ptr.
    intuition.
  Qed.

  Lemma valid_ptr_nodes :
    forall gst gst' p,
      nodes gst = nodes gst' ->
      valid_ptr gst p ->
      valid_ptr gst' p.
  Proof.
    intros.
    eapply valid_ptr_nodes_subset; eauto.
    now find_rewrite.
  Qed.

  Lemma make_pointer_valid :
    forall a,
      id_of (make_pointer a) = hash (addr_of (make_pointer a)).
  Proof.
    by unfold make_pointer.
  Qed.

  Definition valid_ptr_list (gst : global_state) (ps : list pointer) :=
    Forall (valid_ptr gst) ps.

  Lemma valid_ptr_list_nodes_subset :
    forall gst gst' ps,
      valid_ptr_list gst ps ->
      (forall n, In n (nodes gst) -> In n (nodes gst')) ->
      valid_ptr_list gst' ps.
  Proof.
    intros.
    apply Forall_forall.
    intros.
    eapply valid_ptr_nodes_subset; eauto.
    find_eapply_lem_hyp Forall_forall; eauto.
  Qed.

  Lemma valid_ptr_list_nodes :
    forall gst gst' ps,
      nodes gst = nodes gst' ->
      valid_ptr_list gst ps ->
      valid_ptr_list gst' ps.
  Proof.
    intros.
    eapply valid_ptr_list_nodes_subset; eauto.
    now find_rewrite.
  Qed.

  Inductive lift_pred_opt {A} (P : A -> Prop) : option A -> Prop :=
  | LiftPredOptSome : forall a, P a -> lift_pred_opt P (Some a)
  | LiftPredOptNone : lift_pred_opt P None.

  Ltac inv_lift_pred_opt :=
    match goal with
    | [ H: lift_pred_opt _ _ |- _ ] => inv H
    end.

  Lemma lift_pred_opt_elim :
    forall A (P : A -> Prop) o,
      lift_pred_opt P o ->
      (exists a, o = Some a /\ P a) \/
      o = None.
  Proof.
    intros.
    inv H; [left | right]; eexists; eauto.
  Qed.

  Definition valid_opt_ptr (gst : global_state) : option pointer -> Prop :=
    lift_pred_opt (valid_ptr gst).

  Lemma valid_opt_ptr_elim :
    forall gst o,
      valid_opt_ptr gst o ->
      (exists p, o = Some p /\ valid_ptr gst p) \/
      o = None.
  Proof.
    eauto using lift_pred_opt_elim.
  Qed.

  Inductive valid_ptr_payload (gst : global_state) : payload -> Prop :=
  | VPBusy : valid_ptr_payload gst Busy
  | VPGetBestPredecessor : forall p,
      valid_ptr gst p ->
      valid_ptr_payload gst (GetBestPredecessor p)
  | VPGotBestPredecessor : forall p,
      valid_ptr gst p ->
      valid_ptr_payload gst (GotBestPredecessor p)
  | VPGetSuccList : valid_ptr_payload gst GetSuccList
  | VPGotSuccList : forall ps,
      valid_ptr_list gst ps ->
      valid_ptr_payload gst (GotSuccList ps)
  | VPGetPredAndSuccs : valid_ptr_payload gst GetPredAndSuccs
  | VPGotPredAndSuccs : forall p ps,
      valid_opt_ptr gst p ->
      valid_ptr_list gst ps ->
      valid_ptr_payload gst (GotPredAndSuccs p ps)
  | VPNotify : valid_ptr_payload gst Notify
  | VPPing : valid_ptr_payload gst Ping
  | VPPong : valid_ptr_payload gst Pong.

  Ltac inv_vpp :=
    match goal with
    | [ H: valid_ptr_payload _ _ |- _ ] => inv H
    end.

  Inductive valid_ptr_query (gst : global_state) : query -> Prop :=
  | VPQRectify : forall p, valid_ptr gst p -> valid_ptr_query gst (Rectify p)
  | VPQStabilize : valid_ptr_query gst Stabilize
  | VPQStabilize2 : forall p, valid_ptr gst p -> valid_ptr_query gst (Stabilize2 p)
  | VPQJoin : forall p, valid_ptr gst p -> valid_ptr_query gst (Join p)
  | VPQJoin2 : forall p, valid_ptr gst p -> valid_ptr_query gst (Join2 p).

  Definition valid_ptrs_some_cur_request (gst : global_state) (t : pointer * query * payload) : Prop :=
    let '(p, q, m) := t in
    valid_ptr gst p /\
    valid_ptr_query gst q /\
    valid_ptr_payload gst m.

  Lemma valid_ptrs_some_cur_request_intro :
    forall gst p q m,
      valid_ptr gst p ->
      valid_ptr_query gst q ->
      valid_ptr_payload gst m ->
      valid_ptrs_some_cur_request gst (p, q, m).
  Proof.
    easy.
  Qed.

  Lemma valid_ptrs_some_cur_request_elim :
    forall gst p q m,
      valid_ptrs_some_cur_request gst (p, q, m) ->
      valid_ptr gst p /\
      valid_ptr_query gst q /\
      valid_ptr_payload gst m.
  Proof.
    easy.
  Qed.

  Lemma valid_ptrs_some_cur_request_elim_p :
    forall gst p q m,
      valid_ptrs_some_cur_request gst (p, q, m) ->
      valid_ptr gst p.
  Proof.
    unfold valid_ptrs_some_cur_request.
    easy.
  Qed.

  Lemma valid_ptrs_some_cur_request_elim_q :
    forall gst p q m,
      valid_ptrs_some_cur_request gst (p, q, m) ->
      valid_ptr_query gst q.
  Proof.
    unfold valid_ptrs_some_cur_request.
    easy.
  Qed.

  Lemma valid_ptrs_some_cur_request_elim_m :
    forall gst p q m,
      valid_ptrs_some_cur_request gst (p, q, m) ->
      valid_ptr_payload gst m.
  Proof.
    unfold valid_ptrs_some_cur_request.
    easy.
  Qed.

  Definition valid_ptrs_cur_request (gst : global_state) : option (pointer * query * payload) -> Prop :=
    lift_pred_opt (valid_ptrs_some_cur_request gst).

  Definition valid_ptrs_state (gst : global_state) (d : data) :=
    valid_ptr gst (ptr d) /\
    valid_opt_ptr gst (pred d) /\
    Forall (valid_ptr gst) (succ_list d) /\
    valid_ptr gst (known d) /\
    valid_opt_ptr gst (rectify_with d) /\
    valid_ptrs_cur_request gst (cur_request d).

  Definition valid_ptrs_state_elim :
    forall gst d,
      (valid_ptrs_state gst d -> valid_ptr gst (ptr d)) /\
      (valid_ptrs_state gst d -> valid_opt_ptr gst (pred d)) /\
      (valid_ptrs_state gst d -> Forall (valid_ptr gst) (succ_list d)) /\
      (valid_ptrs_state gst d -> valid_ptr gst (known d)) /\
      (valid_ptrs_state gst d -> valid_opt_ptr gst (rectify_with d)) /\
      (valid_ptrs_state gst d -> valid_ptrs_cur_request gst (cur_request d)).
  Proof.
    unfold valid_ptrs_state.
    tauto.
  Qed.

  Definition valid_ptrs_net (gst : global_state) : Prop :=
    forall src dst p,
      In (src, (dst, p)) (msgs gst) ->
      valid_ptr_payload gst p.

  Lemma valid_ptrs_net_elim_snd_snd :
    forall gst m,
      valid_ptrs_net gst ->
      In m (msgs gst) ->
      valid_ptr_payload gst (snd (snd m)).
  Proof.
    unfold valid_ptrs_net.
    intros.
    destruct m.
    destruct p.
    eauto.
  Qed.

  Inductive valid_ptr_timeout (gst : global_state) : timeout -> Prop :=
  | VPTRequest : forall h p, valid_ptr_payload gst p -> valid_ptr_timeout gst (Request h p)
  | VPTick : valid_ptr_timeout gst Tick
  | VPTKeepaliveTick : valid_ptr_timeout gst KeepaliveTick.

  Ltac inv_vpt :=
    match goal with
    | [ H: valid_ptr_timeout _ _ |- _ ] => inv H
    end.

  Definition valid_ptrs_timeouts (gst : global_state) (ts : list timeout) : Prop :=
    Forall (valid_ptr_timeout gst) ts.

  Lemma valid_ptrs_timeouts_intro :
    forall gst h,
      (forall t, In t (timeouts gst h) -> valid_ptr_timeout gst t) ->
      valid_ptrs_timeouts gst (timeouts gst h).
  Proof.
    intros.
    now apply Forall_forall.
  Qed.

  Lemma valid_ptrs_timeouts_elim :
    forall gst h,
      valid_ptrs_timeouts gst (timeouts gst h) ->
      forall t,
        In t (timeouts gst h) ->
        valid_ptr_timeout gst t.
  Proof.
    unfold valid_ptrs_timeouts.
    intros until 1.
    now apply Forall_forall.
  Qed.

  Inductive valid_ptr_event (gst : global_state) : event -> Prop :=
  | VPEsend : forall src dst p, valid_ptr_payload gst p -> valid_ptr_event gst (e_send (src, (dst, p)))
  | VPErecv : forall src dst p, valid_ptr_payload gst p -> valid_ptr_event gst (e_recv (src, (dst, p)))
  | VPEtimeout : forall h t, valid_ptr_timeout gst t -> valid_ptr_event gst (e_timeout h t)
  | VPEfail : forall h, valid_ptr_event gst (e_fail h).

  Definition valid_ptrs_trace (gst : global_state) : Prop :=
    Forall (valid_ptr_event gst) (trace gst).

  Lemma valid_ptrs_trace_intro :
    forall gst,
      (forall e, In e (trace gst) -> valid_ptr_event gst e) ->
      valid_ptrs_trace gst.
  Proof.
    intros.
    now apply Forall_forall.
  Qed.

  Definition valid_ptrs_global (gst : global_state) : Prop :=
    (forall h, valid_ptrs_timeouts gst (timeouts gst h)) /\
    (forall h, lift_pred_opt (valid_ptrs_state gst) (sigma gst h)) /\
    valid_ptrs_net gst /\
    valid_ptrs_trace gst.

  Lemma valid_ptrs_global_elim :
    forall gst,
      valid_ptrs_global gst ->
      (forall h, valid_ptrs_timeouts gst (timeouts gst h)) /\
      (forall h, lift_pred_opt (valid_ptrs_state gst) (sigma gst h)) /\
      valid_ptrs_net gst /\
      valid_ptrs_trace gst.
  Proof.
    auto.
  Qed.

  Ltac copy_elim_valid_ptrs_global :=
    match goal with
    | [ H : valid_ptrs_global _ |- _ ] =>
      copy_apply valid_ptrs_global_elim H;
        break_and
    end.

  Lemma valid_opt_ptr_nodes_subset :
    forall gst gst' o,
      valid_opt_ptr gst o ->
      (forall n, In n (nodes gst) -> In n (nodes gst')) ->
      valid_opt_ptr gst' o.
  Proof.
    intros.
    find_eapply_lem_hyp valid_opt_ptr_elim.
    break_or_hyp; try constructor.
    break_exists; break_and; subst_max.
    constructor.
    eauto using valid_ptr_nodes_subset.
  Qed.

  Lemma valid_opt_ptr_nodes :
    forall gst gst' o,
      nodes gst = nodes gst' ->
      valid_opt_ptr gst o ->
      valid_opt_ptr gst' o.
  Proof.
    intros.
    eapply valid_opt_ptr_nodes_subset; eauto.
    now find_rewrite.
  Qed.

  Lemma valid_ptr_payload_nodes_subset :
    forall gst gst' p,
      valid_ptr_payload gst p ->
      (forall n, In n (nodes gst) -> In n (nodes gst')) ->
      valid_ptr_payload gst' p.
  Proof.
    intros.
    inv_vpp; constructor;
    eauto using valid_ptr_nodes_subset, valid_ptr_list_nodes_subset, valid_opt_ptr_nodes_subset.
  Qed.

  Lemma valid_ptr_payload_nodes :
    forall gst gst' p,
      nodes gst = nodes gst' ->
      valid_ptr_payload gst p ->
      valid_ptr_payload gst' p.
  Proof.
    intros.
    eapply valid_ptr_payload_nodes_subset; eauto.
    now find_rewrite.
  Qed.

  Lemma valid_ptr_timeout_nodes :
    forall gst gst' t,
      valid_ptr_timeout gst t ->
      nodes gst = nodes gst' ->
      valid_ptr_timeout gst' t.
  Proof.
    intros.
    inv_vpt.
    - constructor.
      eauto using valid_ptr_payload_nodes.
    - constructor.
    - constructor.
  Qed.

  Lemma valid_ptrs_timeouts_nodes_subset_timeouts :
    forall gst gst' h,
      valid_ptrs_timeouts gst (timeouts gst h) ->
      timeouts gst = timeouts gst' ->
      nodes gst = nodes gst' ->
      valid_ptrs_timeouts gst' (timeouts gst' h).
  Abort.

  Lemma valid_ptrs_timeouts_nodes_timeouts :
    forall gst gst' h,
      valid_ptrs_timeouts gst (timeouts gst h) ->
      timeouts gst = timeouts gst' ->
      nodes gst = nodes gst' ->
      valid_ptrs_timeouts gst' (timeouts gst' h).
  Proof.
    intros.
    apply valid_ptrs_timeouts_intro; intros.
    eapply valid_ptr_timeout_nodes; eauto.
    eapply valid_ptrs_timeouts_elim; eauto.
    now repeat find_rewrite.
  Qed.

  Lemma valid_ptrs_global_timeout_handler :
    forall gst h st t st' ms nts cts t0,
      valid_ptrs_global gst ->
      timeout_handler h st t = (st', ms, nts, cts) ->
      In t0 nts ->
      valid_ptr_timeout gst t0.
  Admitted.

  Lemma handle_query_req_busy_definition :
    forall src dst st msg st' ms newts clearedts,
      handle_query_req_busy src dst st msg = (st', ms, newts, clearedts) ->
      st' = delay_query st src msg /\
      ms = [(src, Busy)] /\
      clearedts = [] /\
      ((delayed_queries st = [] /\ newts = [KeepaliveTick]) \/
       (delayed_queries st <> [] /\ newts = [])).
  Proof.
    unfold handle_query_req_busy.
    intros.
    repeat break_match; tuple_inversion; tauto.
  Qed.

  Lemma handle_query_res_definition :
    forall src dst st blank q p st' ms newts clearedts,
      handle_query_res src dst st blank q p = (st', ms, newts, clearedts) ->
      (request_payload p /\
       st' = delay_query st src p /\
       clearedts = [] /\
       (delayed_queries st = [] /\
        newts = [KeepaliveTick]) \/
       (delayed_queries st <> [] /\
        newts = [])) \/
      (p = Busy /\
       st' = st /\
       newts = timeouts_in st /\
       clearedts = timeouts_in st) \/
      (exists n,
          q = Rectify n /\
          p = Pong /\
          (exists pr,
              pred st = Some pr /\
              end_query dst (handle_rectify st pr n) = (st', ms, newts, clearedts)) \/
          (pred st = None /\
           end_query dst (update_pred st n, [], [], []) = (st', ms, newts, clearedts))) \/
      (q = Stabilize /\
       (exists new_succ succs,
           p = GotPredAndSuccs (Some new_succ) succs /\
           handle_stabilize dst (make_pointer src) st q new_succ succs = (st', ms, newts, clearedts)) \/
       (exists succs,
           p = GotPredAndSuccs None succs /\
           end_query dst (st, [], [], []) = (st', ms, newts, clearedts))) \/
      (exists new_succ,
          q = Stabilize2 new_succ /\
          exists succs,
            p = GotSuccList succs /\
            end_query dst (update_succ_list st (make_succs SUCC_LIST_LEN new_succ succs),
                           [(addr_of new_succ, Notify)], [], []) = (st', ms, newts, clearedts)) \/
      (exists k,
          q = Join k /\
          (exists bestpred,
              p = GotBestPredecessor bestpred /\
              clearedts = [Request src (GetBestPredecessor (make_pointer dst))] /\
              st' = st /\
              (addr_of bestpred = src /\
               ms = [(src, GetSuccList)] /\
               newts = [Request src GetSuccList]) \/
              (addr_of bestpred <> src /\
               ms = [(addr_of bestpred, (GetBestPredecessor (make_pointer dst)))] /\
               newts = [Request (addr_of bestpred) (GetBestPredecessor (make_pointer dst))])) \/
          (p = GotSuccList [] /\
           end_query dst (st, [], [], []) = (st', ms, newts, clearedts)) \/
          (exists new_succ rest,
              p = GotSuccList (new_succ :: rest) /\
              start_query (addr_of new_succ) st (Join2 new_succ) = (st', ms, newts, clearedts))) \/
      (exists new_succ succs,
          q = Join2 new_succ /\
          p = GotSuccList succs /\
          add_tick (end_query dst (update_for_join st (make_succs SUCC_LIST_LEN new_succ succs), [], [], [])) = (st', ms, newts, clearedts)) \/
      st' = st /\ ms = [] /\ newts = [] /\ clearedts = [].
  Proof.
    unfold handle_query_res.
    intros.
    repeat break_match; try tuple_inversion; try tauto.
    - right. right. left. eexists. intuition eauto.
    - intuition eauto.
    - intuition eauto.
    - intuition eauto.
    - intuition eauto.
    - do 5 right. left.
      exists p0. left. firstorder.
      eexists; intuition eauto.
    - do 5 right. left.
      exists p0. intuition eauto.
    - repeat find_rewrite.
      do 5 right. left.
      exists p0. right.
      intuition.
    - do 5 right. left.
      exists p0.
      intuition eauto.
    - intuition eauto.
  Qed.

  Lemma recv_handler_definition :
    forall src dst st p st' ms newts clearedts,
      recv_handler src dst st p = (st', ms, newts, clearedts) ->
      p = Ping /\
      st' = st /\
      ms = [(src, Pong)] /\
      newts = [] /\
      clearedts = [] \/

      p = Notify /\
      st' = set_rectify_with st (make_pointer src) /\
      ms = [] /\
      newts = [] /\
      clearedts = [] \/

      (exists qd q qm,
          cur_request st = Some (qd, q, qm) /\
          (request_payload p /\
           st' = delay_query st src p /\
           clearedts = [] /\
           (delayed_queries st = [] /\
            newts = [KeepaliveTick]) \/
           (delayed_queries st <> [] /\
            newts = [])) \/
          (p = Busy /\
           st' = st /\
           newts = timeouts_in st /\
           clearedts = timeouts_in st) \/
          (exists n,
              q = Rectify n /\
              p = Pong /\
              (exists pr,
              pred st = Some pr /\
              end_query dst (handle_rectify st pr n) = (st', ms, newts, clearedts)) \/
          (pred st = None /\
           end_query dst (update_pred st n, [], [], []) = (st', ms, newts, clearedts))) \/
      (q = Stabilize /\
       (exists new_succ succs,
           p = GotPredAndSuccs (Some new_succ) succs /\
           handle_stabilize dst (make_pointer src) st q new_succ succs = (st', ms, newts, clearedts)) \/
       (exists succs,
           p = GotPredAndSuccs None succs /\
           end_query dst (st, [], [], []) = (st', ms, newts, clearedts))) \/
      (exists new_succ,
          q = Stabilize2 new_succ /\
          exists succs,
            p = GotSuccList succs /\
            end_query dst (update_succ_list st (make_succs SUCC_LIST_LEN new_succ succs),
                           [(addr_of new_succ, Notify)], [], []) = (st', ms, newts, clearedts)) \/
      (exists k,
          q = Join k /\
          (exists bestpred,
              p = GotBestPredecessor bestpred /\
              clearedts = [Request src (GetBestPredecessor (make_pointer dst))] /\
              st' = st /\
              (addr_of bestpred = src /\
               ms = [(src, GetSuccList)] /\
               newts = [Request src GetSuccList]) \/
              (addr_of bestpred <> src /\
               ms = [(addr_of bestpred, (GetBestPredecessor (make_pointer dst)))] /\
               newts = [Request (addr_of bestpred) (GetBestPredecessor (make_pointer dst))])) \/
          (p = GotSuccList [] /\
           end_query dst (st, [], [], []) = (st', ms, newts, clearedts)) \/
          (exists new_succ rest,
              p = GotSuccList (new_succ :: rest) /\
              start_query (addr_of new_succ) st (Join2 new_succ) = (st', ms, newts, clearedts))) \/
      (exists new_succ succs,
          q = Join2 new_succ /\
          p = GotSuccList succs /\
          add_tick (end_query dst (update_for_join st (make_succs SUCC_LIST_LEN new_succ succs), [], [], [])) = (st', ms, newts, clearedts)) \/
      st' = st /\ ms = [] /\ newts = [] /\ clearedts = []
      ) \/

      (cur_request st = None /\
       st' = st /\
       clearedts = [] /\
       newts = [] /\
       ((exists h,
           p = GetBestPredecessor h /\
           ms = [(src, GotBestPredecessor (best_predecessor (ptr st) (succ_list st) (id_of h)))]) \/
       (p = GetSuccList /\
        ms = [(src, GotSuccList (succ_list st))]) \/
       (p = GetPredAndSuccs /\
        ms = [(src, GotPredAndSuccs (pred st) (succ_list st))]))) \/

      st = st' /\ ms = [] /\ newts = [] /\ clearedts = [].
  Proof.
    unfold recv_handler.
    intros.
    break_if.
    - unfold handle_safe_msg, handle_notify in *.
      find_apply_lem_hyp safe_msgs; break_or_hyp;
      tuple_inversion; intuition.
    - repeat break_match.
      + find_eapply_lem_hyp handle_query_req_busy_definition.
        repeat break_and.
        find_apply_lem_hyp is_request_same_as_request_payload.
        do 2 right. left.
        repeat eexists; left; split; eauto.
        repeat split.
        repeat break_and.
        break_or_hyp; intuition eauto.
      + find_eapply_lem_hyp handle_query_res_definition.
        do 2 right. left.
        repeat eexists; intuition eauto.
      + unfold handle_query_req in *.
        break_match;
          try discriminate;
          repeat find_inversion;
          try tuple_inversion;
          intuition eauto.
      + tuple_inversion; intuition eauto.
      + tuple_inversion; intuition eauto.
  Qed.

  Lemma In_timeouts_in :
    forall t st,
      In t (timeouts_in st) ->
      exists dst q m,
        cur_request st = Some (dst, q, m) /\
        t = Request (addr_of dst) m.
  Proof.
    unfold timeouts_in.
    intros.
    repeat break_match.
    repeat eexists; eauto.
    match type of H with
    | In _ _ => inv H
    end.
    eauto.
    exfalso; auto with *.
    exfalso; auto with *.
  Qed.

  Lemma lift_pred_opt_Some_elim :
    forall A x (P : A -> Prop) a,
      lift_pred_opt P x ->
      x = Some a ->
      P a.
  Proof.
    intros.
    match type of H with
    | lift_pred_opt _ _ => inv H
    end; congruence.
  Qed.

  Lemma try_rectify_definition :
    forall h st ms nts cts st' ms' nts' cts',
      try_rectify h (st, ms, nts, cts) = (st', ms', nts', cts') ->
      (joined st = true /\
       (exists new,
           rectify_with st = Some new /\
           (exists x sq_ms sq_nts sq_cts,
               pred st = Some x /\
               start_query h (clear_rectify_with st) (Rectify new) = (st', sq_ms, sq_nts, sq_cts) /\
               ms' = ms ++ sq_ms /\
               nts' = nts ++ sq_nts /\
               cts' = cts ++ sq_cts) \/
           (pred st = None /\
            st' = clear_rectify_with (update_pred st new) /\
            ms' = ms /\
            nts' = nts /\
            cts' = cts))) \/
      ((joined st = false \/ rectify_with st = None) /\
       (st', ms', nts', cts') = (st, ms, nts, cts)).
  Proof.
    unfold try_rectify.
    intros.
    repeat break_match; tuple_inversion.
    - left.
      split; eauto.
      intuition eauto.
      exists p.
      left.
      intuition eauto.
      repeat eexists; intuition eauto.
    - left.
      split; try tauto.
      eexists; right; split; eauto.
    - tauto.
    - tauto.
  Qed.

  Lemma start_query_definition : 
    forall h st k st' ms nts cts,
      start_query h st k = (st', ms, nts, cts) ->
      (exists dst msg,
          make_request hash h st k = Some (dst, msg) /\
          st' = update_query st dst k msg /\
          ms = [(addr_of dst, msg)] /\
          nts = [Request (addr_of dst) msg] /\
          cts = timeouts_in st) \/
      (make_request hash h st k = None /\
       st' = st /\
       ms = [] /\
       ms = [] /\
       nts = [] /\
       cts = []).
  Proof.
    unfold start_query.
    intros.
    repeat break_match; tuple_inversion; try tauto.
    left; repeat eexists.
  Qed.

  Lemma handle_delayed_queries_definition :
    forall h st st' ms nts cts,
     handle_delayed_queries h st = (st', ms, nts, cts) ->
     st' = clear_delayed_queries st /\
     ms = concat (map (handle_delayed_query h st) (delayed_queries st)) /\
     nts = [] /\
     cts = [KeepaliveTick].
  Proof.
    unfold handle_delayed_queries.
    intros.
    tuple_inversion.
    intuition eauto.
  Qed.

  Lemma end_query_definition :
    forall h st ms newts clearedts st' ms' newts' clearedts',
      end_query h (st, ms, newts, clearedts) = (st', ms', newts', clearedts') ->
      exists st'' ms'',
        handle_delayed_queries h (clear_query st) = (st'', ms'', [], [KeepaliveTick]) /\
        try_rectify h (st'', ms'' ++ ms, newts, timeouts_in st ++ [KeepaliveTick] ++ clearedts) = (st', ms', newts', clearedts').
  Proof.
    unfold end_query.
    intros.
    repeat break_let.
    find_apply_lem_hyp handle_delayed_queries_definition.
    repeat (break_and || break_or_hyp || break_exists).
    subst_max.
    repeat eexists; eauto.
  Qed.

  Lemma handle_rectify_definition :
    forall st my_pred notifier st' ms nts cts,
      handle_rectify st my_pred notifier = (st', ms, nts, cts) ->
      ms = [] /\
      nts = [] /\
      cts = [] /\
      (between (id_of my_pred) (id_of notifier) (id_of (ptr st)) /\
       st' = update_pred st notifier \/
       ~ between (id_of my_pred) (id_of notifier) (id_of (ptr st)) /\
       st' = st).
  Proof.
    unfold handle_rectify.
    intros.
    rewrite between_between_bool_equiv.
    break_if; tuple_inversion; firstorder.
  Qed.

  Ltac expand_def :=
    repeat (try break_or_hyp; try break_and; try break_exists);
    subst_max;
    try tuple_inversion;
    try (exfalso; tauto).

  Lemma valid_ptrs_global_recv_handler :
    forall gst xs m ys d st ms newts clearedts,
      valid_ptrs_global gst ->
      msgs gst = xs ++ m :: ys ->
      In (fst (snd m)) (nodes gst) ->
      ~ In (fst (snd m)) (failed_nodes gst) ->
      sigma gst (fst (snd m)) = Some d ->
      recv_handler (fst m) (fst (snd m)) d (snd (snd m)) = (st, ms, newts, clearedts) ->
      forall t, In t newts ->
           valid_ptr_timeout gst t.
  Proof.
    intros.
    find_apply_lem_hyp recv_handler_definition.
    find_apply_lem_hyp valid_ptrs_global_elim; break_and.
    assert (valid_ptr_payload gst (snd (snd m))).
    { apply valid_ptrs_net_elim_snd_snd;
      try find_rewrite; auto with datatypes. }
    expand_def.
    - find_apply_lem_hyp in_inv.
      break_or_hyp; try (exfalso; auto with *; fail).
      constructor.
    - find_apply_lem_hyp In_timeouts_in.
      break_exists; break_and; subst_max.
      constructor.
      assert (valid_ptrs_state gst d).
      { pose proof (H6 (fst (snd m))).
        find_eapply_lem_hyp lift_pred_opt_Some_elim; eauto. }
      find_apply_lem_hyp valid_ptrs_state_elim.
      find_rewrite.
      inv H10.
      simpl in *; tauto.
    - break_and.
      destruct (handle_rectify _ _ _) eqn:H_rectify.
      repeat destruct p.
      find_eapply_lem_hyp end_query_definition.
      break_exists.
      break_and.
      find_apply_lem_hyp try_rectify_definition.
      expand_def; try (exfalso; tauto).
      + find_apply_lem_hyp start_query_definition.
        find_apply_lem_hyp handle_rectify_definition.
        expand_def;
          try (find_apply_lem_hyp in_inv;
                break_or_hyp; try (exfalso; eauto using in_nil; fail)).
        * constructor.
          simpl in *.
          break_match; find_inversion || congruence.
          constructor.
        * constructor.
          simpl in *.
          break_match; find_inversion || congruence.
          constructor.
      + find_eapply_lem_hyp handle_rectify_definition.
        expand_def; exfalso; tauto.
      + find_eapply_lem_hyp handle_rectify_definition.
        expand_def; exfalso; tauto.
      + find_eapply_lem_hyp handle_rectify_definition.
        expand_def; exfalso; tauto.
    - find_eapply_lem_hyp end_query_definition; expand_def.
      find_eapply_lem_hyp try_rectify_definition; expand_def;
      try (exfalso; tauto).
      + simpl in *.
        find_eapply_lem_hyp start_query_definition; expand_def;
        simpl in *; try break_or_hyp; try (exfalso; tauto).
        break_match.
        * find_inversion.
          do 2 constructor.
        * discriminate.
    - admit. (* handle_stabilize *)
    - find_eapply_lem_hyp end_query_definition.
      expand_def.
      find_eapply_lem_hyp try_rectify_definition.
      expand_def.
      simpl in *.
      find_eapply_lem_hyp start_query_definition.
      expand_def.
      simpl in *; break_or_hyp; try (exfalso; tauto).
      break_match; try discriminate.
      repeat find_inversion.
      do 2 constructor.
    - find_eapply_lem_hyp end_query_definition.
      expand_def.
      find_eapply_lem_hyp try_rectify_definition.
      expand_def.
      simpl in *.
      find_eapply_lem_hyp start_query_definition.
      expand_def.
      simpl in *; break_or_hyp; try (exfalso; tauto).
      break_match; try discriminate.
      repeat find_inversion.
      do 2 constructor.
    - simpl in *; break_or_hyp; try (exfalso; tauto).
      do 2 constructor.
    - simpl in *; break_or_hyp; try (exfalso; tauto).
      do 2 constructor.
      apply valid_ptr_intro.
      + apply make_pointer_valid.
      + assumption.
    - find_eapply_lem_hyp end_query_definition.
      expand_def.
      find_eapply_lem_hyp try_rectify_definition.
      expand_def.
      simpl in *.
      find_eapply_lem_hyp start_query_definition.
      expand_def.
      simpl in *; break_or_hyp; try (exfalso; tauto).
      break_match; try discriminate.
      repeat find_inversion.
      do 2 constructor.
    - find_eapply_lem_hyp start_query_definition.
      expand_def.
      simpl in *; break_or_hyp; try (exfalso; tauto).
      repeat find_inversion.
      do 2 constructor.
    - admit. (* add_tick on end_query *)
  Admitted.

  Lemma valid_ptrs_global_timeouts :
    forall gst gst',
      valid_ptrs_global gst ->
      step_dynamic gst gst' ->
      forall h,
        valid_ptrs_timeouts gst' (timeouts gst' h).
  Proof.
    intros.
    copy_elim_valid_ptrs_global.
    break_step.
    - apply valid_ptrs_timeouts_intro; intros.
      unfold update_for_start in *.
      repeat break_let.
      simpl in *.
      tuple_inversion.
      simpl in *.
      destruct t; constructor.
      destruct (addr_eq_dec h h0).
      + find_erewrite_lem update_eq.
        find_apply_lem_hyp in_inv.
        break_or_hyp.
        * find_inversion.
          constructor.
          (* question: can I make this eauto not work? *)
          apply valid_ptr_intro; simpl; eauto.
        * exfalso; auto using in_nil.
      + find_erewrite_lem update_diff.
        find_apply_lem_hyp valid_ptrs_global_elim.
        break_and.
        find_apply_lem_hyp valid_ptrs_timeouts_elim; eauto.
        inversion H7; subst_max.
        eapply valid_ptr_payload_nodes_subset; simpl; eauto.
    - eauto using valid_ptrs_timeouts_nodes_timeouts.
    - apply valid_ptrs_timeouts_intro; intros.
      eapply valid_ptr_timeout_nodes;
        try eapply apply_handler_result_preserves_nodes; eauto.
      find_apply_lem_hyp apply_handler_result_In_timeouts;
        repeat (break_and || break_or_hyp);
        eauto using valid_ptrs_global_timeout_handler,
                    valid_ptr_timeout_nodes,
                    valid_ptrs_timeouts_elim.
    - apply valid_ptrs_timeouts_intro; intros.
      eapply valid_ptr_timeout_nodes;
        try eapply apply_handler_result_preserves_nodes; eauto.
      find_apply_lem_hyp apply_handler_result_In_timeouts;
        repeat (break_and || break_or_hyp);
        eauto using valid_ptrs_global_recv_handler,
                    valid_ptr_timeout_nodes,
                    valid_ptrs_timeouts_elim.
  Qed.

  Lemma valid_ptrs_global_sigma :
    forall gst gst',
      valid_ptrs_global gst ->
      step_dynamic gst gst' ->
      forall h d,
        sigma gst' h = Some d ->
        valid_ptrs_state gst' d.
  Proof.
    intros.
    break_step.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma valid_ptrs_global_net :
    forall gst gst',
      valid_ptrs_global gst ->
      step_dynamic gst gst' ->
      valid_ptrs_net gst'.
  Proof.
    intros.
    break_step.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma valid_ptrs_global_trace :
    forall gst gst',
      valid_ptrs_global gst ->
      step_dynamic gst gst' ->
      valid_ptrs_trace gst'.
  Proof.
    intros.
    break_step.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem valid_ptrs_global_inductive :
    forall gst,
      reachable_st gst ->
      valid_ptrs_global gst.
  Proof.
    intros.
    induct_reachable_st.
    - admit.
    - unfold valid_ptrs_global; repeat break_and_goal.
      + eapply valid_ptrs_global_timeouts; eauto.
      + intros;
        destruct (sigma _ _) eqn:H_st;
        constructor;
        eapply valid_ptrs_global_sigma; eauto.
      + eapply valid_ptrs_global_net; eauto.
      + eapply valid_ptrs_global_trace; eauto.
  Admitted.

  Definition query_state_net_invariant_inductive :
    forall gst,
      reachable_st gst ->
      query_state_net_invariant gst.
  Proof.
    intros.
    induct_reachable_st.
    { admit. } (* have to define valid initial states *)
    assert (reachable_st gst') by eauto using reachableStep.
    pose proof (query_state_net_invariant_elim gst IHreachable_st).
    intros until 3.
    split.
    - eapply queries_always_remote; eauto.
    - break_step.
      + (* start case *)
        destruct (addr_eq_dec src h).
        * (* source of query is the joining node *)
          admit.
        * (* it's unrelated *)
          admit.
      + (* fail case *)
        admit.
      + (* timeout case *)
        admit.
      + (* receive case *)
        admit.
  Admitted.

End ChordProof.
