Require Import Arith.
Require Import List.
Import ListNotations.
Require Import StructTact.Dedup.
Require Import StructTact.RemoveAll.

Section Chord.
  Variable SUCC_LIST_LEN : nat.

  Definition addr := nat.
  Definition id := nat.
  Definition pointer := (id * addr)%type.

  Variable hash : addr -> id.
  (* this is never actually true, of course *)
  Variable hash_inj : forall a b : addr,
      hash a = hash b -> a = b.

  Definition addr_eq_dec := Nat.eq_dec.
  Definition id_of (p : pointer) : id := fst p.
  Definition addr_of (p : pointer) : addr := snd p.

  Definition pointer_eq_dec : forall x y : pointer,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality.
  Defined.

  Definition make_pointer (a : addr) : pointer := (hash a, a).

  Inductive payload :=
  | Busy : payload
  | GetBestPredecessor : pointer -> payload
  | GotBestPredecessor : pointer -> payload
  | GetSuccList : payload
  | GotSuccList : list pointer -> payload
  | GetPredAndSuccs : payload
  | GotPredAndSuccs : option pointer -> list pointer -> payload
  | Notify : payload
  | Ping : payload
  | Pong : payload.

  Lemma option_eq_dec : forall A : Type,
    (forall x y : A, {x = y} + {x <> y}) ->
    forall a b : option A, {a = b} + {a <> b}.
  Proof using.
    decide equality.
  Defined.

  Definition payload_eq_dec : forall x y : payload,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality.
  Defined.

  Inductive timeout :=
  | Tick : timeout
  | KeepaliveTick : timeout
  | Request : addr -> payload -> timeout.

  Definition timeout_eq_dec : forall x y : timeout,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality.
  Defined.

  Inductive query :=
  (* needs a pointer to the notifier *)
  | Rectify : pointer -> query
  | Stabilize : query
  (* needs a new successor *)
  | Stabilize2 : pointer -> query
  (* needs a known node *)
  | Join : pointer -> query
  (* needs to know new successor *)
  | Join2 : pointer -> query.

  Record data := mkData { ptr : pointer;
                          pred : option pointer;
                          succ_list : list pointer;
                          known : pointer;
                          joined : bool;
                          rectify_with : option pointer;
                          cur_request : option (pointer * query * payload);
                          delayed_queries : list (addr * payload) }.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Definition is_request (p : payload) : bool :=
    match p with
    | GetBestPredecessor _ => true
    | GetSuccList => true
    | GetPredAndSuccs => true
    | Ping => true
    | _ => false
    end.

  Definition closes_request (req res : payload) : bool :=
    match req, res with
    | GetBestPredecessor _, GotBestPredecessor _ => true
    | GetSuccList, GotSuccList _ => true
    | GetPredAndSuccs, GotPredAndSuccs _ _ => true
    | Ping, Pong => true
    | _, _ => false
    end.

  Definition add_tick (r : res) : res :=
    let '(st, sends, newts, cts) := r in
    (st, sends, Tick :: newts, cts).

  Definition chop_succs (succs : list pointer) : list pointer :=
    firstn SUCC_LIST_LEN succs.

  Definition make_succs (head : pointer) (rest : list pointer) : list pointer :=
    chop_succs (head :: rest).

  Definition update_pred (st : data) (p : pointer) : data :=
    {| ptr := ptr st;
       pred := Some p;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition update_succ_list (st : data) (succs : list pointer) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succs;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition update_query (st : data) (dst : pointer) (q : query) (m : payload) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := Some (dst, q, m);
       delayed_queries := delayed_queries st |}.

  Definition update_for_join (st : data) (succs : list pointer) : data :=
    {| ptr := ptr st;
       pred := None;
       succ_list := succs;
       known := known st;
       joined := true;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition clear_rectify_with (st : data) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := None;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition clear_query (st : data) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := None;
       delayed_queries := delayed_queries st |}.

  Definition clear_delayed_queries (st : data) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := [] |}.

  Definition init_state_preset (h pred : addr) (succs : list addr) : data :=
    {| ptr := make_pointer h;
       pred := Some (make_pointer pred);
       succ_list := chop_succs (map make_pointer succs);
       known := make_pointer pred;
       joined := true;
       rectify_with := None;
       cur_request := None;
       delayed_queries := [] |}.

  Definition init_state_join (h k : addr) : data :=
    {| ptr := make_pointer h;
       pred := None;
       succ_list := [];
       known := make_pointer k;
       joined := false;
       rectify_with := None;
       cur_request := None;
       delayed_queries := [] |}.

  Definition empty_start_res (h : addr) : data * list (addr * payload) * list timeout :=
    ({| ptr := make_pointer h;
        pred := None;
        succ_list := [];
        known := make_pointer h;
        joined := false;
        rectify_with := None;
        cur_request := None;
        delayed_queries := [] |},
     [],
     []).

  (* true iff x in (a, b) on some sufficiently large "circle" *)
  Definition between_bool (a x b : id) : bool :=
    match lt_dec a b, lt_dec a x, lt_dec x b with
    | left _, left _, left _ => true
    | right _, left _, _ => true
    | right _, _, left _ => true
    | _, _, _ => false
    end.

  Definition ptr_between_bool (a x b : pointer) : bool :=
    between_bool (id_of a) (id_of x) (id_of b).

  Definition set_rectify_with (st : data) (rw : pointer) : data :=
    match rectify_with st with
    | Some rw0 =>
      if ptr_between_bool rw0 rw (ptr st)
      then {| ptr := ptr st;
              pred := pred st;
              succ_list := succ_list st;
              known := known st;
              joined := joined st;
              rectify_with := Some rw;
              cur_request := cur_request st;
              delayed_queries := delayed_queries st |}
      else st
    | None => st
    end.

  Definition send_eq_dec :
    forall x y : addr * payload,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality.
  Qed.

  Definition delay_query (st : data) (src : addr) (msg : payload) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := dedup send_eq_dec ((src, msg) :: delayed_queries st) |}.

  Definition make_request (h : addr) (st : data) (k : query) : option (pointer * payload) :=
    match k with
    | Rectify notifier =>
      option_map (fun p => (p, Ping)) (pred st)
    | Stabilize =>
      option_map (fun succ => (succ, GetPredAndSuccs)) (hd_error (succ_list st))
    | Stabilize2 new_succ =>
      Some (new_succ, GetSuccList)
    | Join known =>
      Some (known, GetBestPredecessor (make_pointer h))
    | Join2 new_succ =>
      Some (new_succ, GetSuccList)
    end.

  Definition timeouts_in (st : data) : list timeout :=
    match cur_request st with
    | Some (dst, _, m) => [Request (addr_of dst) m]
    | None => []
    end.

  Definition start_query (h : addr) (st : data) (k : query) : res :=
    let cst := timeouts_in st in
    match make_request h st k with
    | Some (dst, msg) =>
      (update_query st dst k msg,
       [(addr_of dst, msg)],
       [Request (addr_of dst) msg],
       cst)
    | None =>
      (* only happens if succ_list = [], which is contra protocol assumptions *)
      (st, [], [], [])
    end.

  Definition do_rectify (h : addr) (st : data) : res :=
    match joined st, cur_request st, rectify_with st with
    | true, None, Some new =>
      let st := clear_rectify_with st in
      match pred st with
      | Some _ => start_query h st (Rectify new)
      | None => (update_pred st new, [], [], [])
      end
    | _, _, _ => (st, [], [], [])
    end.

  Definition best_predecessor (h : pointer) (succs : list pointer) (them : pointer) : pointer :=
    hd h (filter (fun s => ptr_between_bool h s them)
                 (rev succs)).

  Definition handle_query_req (st : data) (src : addr) (msg : payload) : list (addr * payload) :=
    match msg with
    | GetSuccList =>
      [(src, GotSuccList (succ_list st))]
    | GetPredAndSuccs =>
      [(src, GotPredAndSuccs (pred st) (succ_list st))]
    | GetBestPredecessor p =>
      [(src, GotBestPredecessor (best_predecessor (ptr st) (succ_list st) p))]
    | _ => []
    end.

  Definition handle_delayed_query (h : addr) (st : data) (q : addr * payload) : list (addr * payload) :=
    let (src, msg) := q in
    handle_query_req st src msg.

  Definition do_delayed_queries (h : addr) (st : data) : res :=
    match cur_request st with
    | Some _ => (st, [], [], [])
    | None =>
      let sends := concat (map (handle_delayed_query h st) (delayed_queries st)) in
      (clear_delayed_queries st, sends, [], [KeepaliveTick])
    end.

  (* need to prove that this never gets called with requests in the sends of r *)
  Definition end_query (r : res) : res :=
    let '(st, outs, nts, cts) := r in
    let clearreq := timeouts_in st in
    let st' := clear_query st in
    (st', outs, nts, clearreq ++ cts).

  Definition ptrs_to_addrs : list (pointer * payload) -> list (addr * payload) :=
    map (fun p => (addr_of (fst p), (snd p))).

  Definition handle_rectify (st : data) (my_pred : pointer) (notifier : pointer) : res :=
    if ptr_between_bool my_pred notifier (ptr st)
    then (update_pred st notifier, [], [], [])
    else (st, [], [], []).

  Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : pointer) (succs : list pointer) : res :=
    let new_st := update_succ_list st (make_succs src succs) in
    if ptr_between_bool (ptr st) new_succ src
    then start_query h new_st (Stabilize2 new_succ)
    else end_query (new_st, [(addr_of src, Notify)], [], []).

  Definition next_msg_for_join (self : pointer) (src best_pred : addr) : payload :=
    if addr_eq_dec best_pred src
    then GetSuccList
    else GetBestPredecessor self.

  Definition handle_query_res (src h : addr) (st : data) (q : query) (p : payload) : res :=
    match q, p with
    | Rectify notifier, Pong =>
      match pred st with
      | Some p => end_query (handle_rectify st p notifier)
      | None => end_query (update_pred st notifier, [], [], [])
      end
    | Stabilize, GotPredAndSuccs new_succ succs =>
      match new_succ with
      | Some ns => (handle_stabilize h (make_pointer src) st q ns succs)
      | None => end_query (st, [], [], [])
      end
    | Stabilize2 new_succ, GotSuccList succs =>
      end_query (update_succ_list st (make_succs new_succ succs),
                 [(addr_of new_succ, Notify)],
                 [],
                 [])
    | Join known, GotBestPredecessor best_pred =>
      let a := addr_of best_pred in
      let req := next_msg_for_join (ptr st) src a in
      (st,
       [(a, req)],
       [Request a req],
       [Request src (GetBestPredecessor (ptr st))])
    | Join known, GotSuccList l =>
      match l with
      | (new_succ :: _) => start_query (addr_of new_succ) st (Join2 new_succ)
      | [] => end_query (st, [], [], []) (* this is bad *)
      end
    | Join2 new_succ, GotSuccList l =>
      let succs := make_succs new_succ l in
      add_tick (end_query (update_for_join st succs, [], [], []))
    | _, Busy => (st, [], timeouts_in st, timeouts_in st)
    | _, _ => (st, [], [], [])
    end.

  Definition handle_query_req_busy (src : addr) (st : data) (msg : payload) : res :=
    if list_eq_dec send_eq_dec (delayed_queries st) nil
    then (delay_query st src msg, [(src, Busy)], [KeepaliveTick], [])
    else (delay_query st src msg, [(src, Busy)], [], []).

  Definition is_safe (msg : payload) :=
    match msg with
    | Notify => true
    | Ping => true
    | _ => false
    end.

  Definition handle_msg (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    match msg, cur_request st, is_request msg with
    | Notify, _, _ => (set_rectify_with st (make_pointer src), [], [], [])
    | Ping, _, _ => (st, [(src, Pong)], [], [])
    | _, Some (query_dst, q, _), true => handle_query_req_busy src st msg
    | _, Some (query_dst, q, _), false => handle_query_res src dst st q msg
    | _, None, _ => (st, handle_query_req st src msg, [], [])
    end.

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    let '(st, ms1, nts1, cts1) := handle_msg src dst st msg in
    let '(st, ms2, nts2, cts2) := do_delayed_queries dst st in
    let '(st, ms3, nts3, cts3) := do_rectify dst st in
    let nts := nts3 ++ remove_all timeout_eq_dec cts3
                    (nts2 ++ remove_all timeout_eq_dec cts2 nts1) in
    (st, ms3 ++ ms2 ++ ms1, nts, cts1 ++ cts2 ++ cts3).

  Definition pi {A B C D : Type} (t : A * B * C * D) : A * B * C :=
    let '(a, b, c, d) := t in (a, b, c).

  Definition start_handler (h : addr) (knowns : list addr) : data * list (addr * payload) * list timeout :=
    match knowns with
    | k :: [] =>
      pi (start_query h (init_state_join h k) (Join (make_pointer k)))
    | k :: nowns =>
      (init_state_preset h k nowns, [], [Tick])
    (* garbage data, shouldn't happen *)
    | [] => empty_start_res h
    end.

  Definition tick_handler (h : addr) (st : data) : res :=
    match cur_request st, joined st with
    | None, true => add_tick (start_query h st Stabilize)
    | _, _ => (st, [], [Tick], [])
    end.

  Definition handle_query_timeout (h : addr) (st : data) (dead : pointer) (q : query) : res :=
    match q with
    | Rectify notifier =>
      end_query (update_pred st notifier, [], [], [])
    | Stabilize =>
      match succ_list st with
      | _ :: rest =>
        start_query h (update_succ_list st rest) Stabilize
      (* will not happen in a good network *)
      | [] =>
        end_query (st, [], [], [])
      end
    | Stabilize2 new_succ =>
      match succ_list st with
      | next :: _ =>
        end_query (st, [(addr_of next, Notify)], [], [])
      (* again, won't happen in a good network *)
      | [] =>
        end_query (st, [], [], [])
      end
    (* Join, Join2 *)
    | _ => end_query (st, [], [], [])
    end.

  Definition send_keepalives (st : data) : list (addr * payload) :=
    map (fun q => (fst q, Busy)) (delayed_queries st).

  Definition keepalive_handler (st : data) : res :=
    (st, send_keepalives st, [KeepaliveTick], []).

  Definition request_timeout_handler (h : addr) (st : data) (dst : addr) (msg : payload) : res :=
    match cur_request st with
    | Some (ptr, q, _) =>
      if addr_eq_dec (addr_of ptr) dst
      then handle_query_timeout h st ptr q
      else (st, [], [], []) (* shouldn't happen *)
    | None => (st, [], [], []) (* shouldn't happen *)
    end.

  Definition timeout_handler (h : addr) (st : data) (t : timeout) : res :=
    match t with
    | Request dst msg => request_timeout_handler h st dst msg
    | Tick => tick_handler h st
    | KeepaliveTick => keepalive_handler st
    end.
End Chord.
