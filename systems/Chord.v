Require Import Arith.
Require Import List.
Import ListNotations.
Require Import StructTact.Dedup.

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
  Proof.
    decide equality; auto using Nat.eq_dec.
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
  Proof.
    decide equality.
  Qed.
  Definition payload_eq_dec : forall x y : payload,
      {x = y} + {x <> y}.
  Proof.
    decide equality; auto using pointer_eq_dec, list_eq_dec, option_eq_dec.
  Defined.

  Inductive timeout :=
  | Tick : timeout
  | KeepaliveTick : timeout
  | Request : addr -> payload -> timeout.
  Definition timeout_eq_dec : forall x y : timeout,
      {x = y} + {x <> y}.
  Proof.
    decide equality; auto using addr_eq_dec, payload_eq_dec.
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

  Record data := Data { ptr : pointer ;
                        pred : option pointer ;
                        succ_list : list pointer ;
                        known : pointer ;
                        joined : bool ;
                        rectify_with : option pointer ;
                        cur_request : option (pointer * query * payload) ;
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
    match req with
      | GetBestPredecessor _ => match res with
                                  | GotBestPredecessor _ => true
                                  | _ => false
                                end
      | GetSuccList => match res with
                         | GotSuccList _ => true
                         | _ => false
                       end
      | GetPredAndSuccs => match res with
                             | GotPredAndSuccs _ _ => true
                             | _ => false
                           end
      | Ping => match res with
                  | Pong => true
                  | _ => false
                end
      | _ => false
    end.

  Definition add_tick (r : res) : res :=
    let '(st, sends, newts, cts) := r in
    (st, sends, Tick :: newts, cts).

  Definition can_be_client (a : addr) := True.
  Definition can_be_node (a : addr) := True.

  Definition update_pred (st : data) (p : pointer) : data := Data (ptr st) (Some p) (succ_list st) (known st) (joined st) (rectify_with st) (cur_request st) (delayed_queries st).

  Definition update_succ_list (st : data) (succs : list pointer) : data := Data (ptr st) (pred st) succs (known st) (joined st) (rectify_with st) (cur_request st) (delayed_queries st).

  Definition update_query (st : data) (dst : pointer) (q : query) (m : payload) : data := Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) (Some (dst, q, m)) (delayed_queries st).

  Definition update_for_join (st : data) (succs : list pointer) : data := Data (ptr st) None succs (known st) true (rectify_with st) (cur_request st) (delayed_queries st).

  Definition set_rectify_with (st : data) (rw : pointer) : data :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (Some rw) (cur_request st) (delayed_queries st).

  Definition clear_rectify_with (st : data) : data :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) None (cur_request st) (delayed_queries st).

  Definition clear_query (st : data) : data :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) None (delayed_queries st).

  Definition send_dec :
    forall x y : addr * payload,
      {x = y} + {x <> y}.
  Proof.
    decide equality.
    - now apply payload_eq_dec.
    - now apply addr_eq_dec.
  Defined.

  Definition delay_query (st : data) (src : addr) (msg : payload) : data :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) (cur_request st) (dedup send_dec ((src, msg) :: delayed_queries st)).

  Definition clear_delayed_queries (st : data) : data :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) (cur_request st) [].

  Definition make_request (h : addr) (st : data) (k : query) : option (pointer * payload) :=
    match k with
      | Rectify notifier => match pred st with
                              | Some p => Some (p, Ping)
                              | None => None
                            end
      | Stabilize => match head (succ_list st) with
                       | Some succ => Some (succ, GetPredAndSuccs)
                       | None => None (* impossible under protocol assumptions but possible irl *)
                     end
      | Stabilize2 new_succ => Some (new_succ, GetSuccList)
      | Join known => Some (known, GetBestPredecessor (make_pointer h))
      | Join2 new_succ => Some (new_succ, GetSuccList)
    end.

  Definition timeouts_in (st : data) : list timeout :=
    match cur_request st with
      | Some (dst, q, m) => [Request (addr_of dst) m]
      | None => []
    end.

  Definition start_query (h : addr) (st : data) (k : query) : res :=
    let cst := timeouts_in st in
    match make_request h st k with
      | Some (dst, msg) => (update_query st dst k msg, [(addr_of dst, msg)], [Request (addr_of dst) msg], cst)
      | None => (st, [], [], []) (* only happens if succ_list = [], which is contra protocol assumptions *)
    end.

  (* something to prove: try_rectify is not invoked unless cur_request st is None *)
  Definition try_rectify (h : addr) (r : res) : res :=
    let '(st, outs, nts, cts) := r in
    if joined st
    then match rectify_with st with
           | Some new => match pred st with
                           | Some _ => let st' := clear_rectify_with st in
                                       let '(st'', outs', nts', cts') := start_query h st' (Rectify new) in
                                       (st'', outs ++ outs', nts ++ nts', cts ++ cts')
                           | None => let st' := clear_rectify_with (update_pred st new) in
                                     (st', outs, nts, cts)
                         end
           | None => r
         end
    else r.

  Definition request_in (msgs : list (addr * payload)) :=
    existsb is_request (map snd msgs).

  (* true iff n in (a, b) on some sufficiently large "circle" *)
  Definition between_bool (a : id) (x : id) (b : id) : bool :=
    if lt_dec a b
    then if (lt_dec a x)
         then if (lt_dec x b)
              then true
              else false
         else false
    else
      if (lt_dec a x)
      then true
      else if (lt_dec x b)
           then true
           else false.

  Definition best_predecessor (h : pointer) (succs : list pointer) (id : id) : pointer :=
    let splits (s : pointer) : bool := between_bool (id_of h) (id_of s) id
    in match head (filter splits (rev succs)) with
         | Some succ => succ
         | None => h
       end.

  Definition handle_query_req (st : data) (msg : payload) : option payload :=
    match msg with
    | GetSuccList => Some (GotSuccList (succ_list st))
    | GetPredAndSuccs => Some (GotPredAndSuccs (pred st) (succ_list st))
    | GetBestPredecessor p => Some (GotBestPredecessor (best_predecessor (ptr st) (succ_list st) (id_of p)))
    | _ => None (* shouldn't happen *)
    end.

  Definition handle_delayed_query (h : addr) (st : data) (q : addr * payload) : list (addr * payload) :=
    let (src, msg) := q in
    match handle_query_req st msg with
      | Some p => [(src, p)]
      | None => []
    end.

  Definition handle_delayed_queries (h : addr) (st : data) : res :=
    let sends := map (handle_delayed_query h st) (delayed_queries st) in
    (clear_delayed_queries st, concat sends, [], [KeepaliveTick]).

  (* need to prove that this never gets called with requests in the sends of r *)
  Definition end_query (h : addr) (r : res) : res :=
    let '(st, outs, nts, cts) := r in
    let st' := clear_query st in
    let '(st'', delayed_sends, nts', cts') := handle_delayed_queries h st' in
    let clearreq := timeouts_in st in
    try_rectify h (st'', delayed_sends ++ outs, nts' ++ nts, clearreq ++ cts' ++ cts).

  Definition ptrs_to_addrs : list (pointer * payload) -> list (addr * payload) :=
    map (fun p => (addr_of (fst p), (snd p))).

  Definition chop_succs (succs : list pointer) : list pointer :=
    firstn SUCC_LIST_LEN succs.

  Definition make_succs (head : pointer) (rest : list pointer) : list pointer :=
    chop_succs (head :: rest).

  Definition handle_rectify (h : addr) (st : data) (my_pred : pointer) (q : query) (notifier : pointer) : res :=
    if between_bool (id_of my_pred) (id_of notifier) (id_of (ptr st))
    then (update_pred st notifier, [], [], [])
    else (st, [], [], []).

  Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : pointer) (succs : list pointer) : res :=
    let new_st := update_succ_list st (make_succs src succs) in
    if between_bool (id_of (ptr st)) (id_of new_succ) (id_of src)
    then start_query h new_st (Stabilize2 new_succ)
    else end_query h (new_st, [(addr_of src, Notify)], [], []).

  Definition handle_query_res (src : addr) (h : addr) (st : data) (qdst : pointer) (q : query) (msg : payload) : res :=
    if payload_eq_dec msg Busy
    then (* refresh the timeout *)
      (st, [], timeouts_in st, timeouts_in st)
    else match q with
         | Rectify notifier =>
           match msg with
           | Pong => match (pred st) with
                     | Some p => end_query h (handle_rectify h st p q notifier)
                     | None => end_query h (update_pred st notifier, [], [], [])
                     end
           | _ => (st, [], [], [])
           end
         | Stabilize =>
           match msg with
           | GotPredAndSuccs new_succ succs =>
             match new_succ with
             | Some ns => (handle_stabilize h (make_pointer src) st q ns succs)
             | None => end_query h (st, [], [], [])
             end
           | _ => (st, [], [], [])
           end
         | Stabilize2 new_succ =>
           match msg with
           | GotSuccList succs => end_query h (update_succ_list st (make_succs new_succ succs),
                                               [(addr_of new_succ, Notify)], [], [])
           | _ => (st, [], [], [])
           end
         | Join known =>
           match msg with
           | GotBestPredecessor p => let a := addr_of p in
                                     let self := make_pointer h in
                                     let gbp := GetBestPredecessor self in
                                     let oldt := Request src gbp in
                                     if addr_eq_dec a src
                                     then (st, [(src, GetSuccList)], [Request src GetSuccList], [oldt])
                                     else (st, [(a, gbp)], [Request a gbp], [oldt])
           | GotSuccList l =>
             match l with
             | [] => end_query h (st, [], [], []) (* this is bad *)
             | (new_succ :: _) => start_query (addr_of new_succ) st (Join2 new_succ)
             end
           | _ => (st, [], [], [])
           end
         | Join2 new_succ =>
           match msg with
           | GotSuccList l => let succs := make_succs new_succ l in
                              add_tick (end_query h (update_for_join st succs, [], [], []))
           | _ => (st, [], [], [])
           end
         end.

  Definition handle_notify (src dst : addr) (st : data) : res :=
    (set_rectify_with st (make_pointer src), [], [], []).

  Definition handle_query_req_busy (src dst : addr) (st : data) (msg : payload) : res :=
    (delay_query st src msg, [(src, Busy)], [KeepaliveTick], []).

  Definition is_safe (msg : payload) :=
    match msg with
    | Notify => true
    | Ping => true
    | _ => false
    end.

  Definition handle_safe_msg (src dst : addr) (st : data) (msg : payload) : res :=
    match msg with
    | Notify => handle_notify src dst st
    | Ping => (st, [(src, Pong)], [], [])
    | _ => (st, [], [], [])
    end.

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    if is_safe msg
    then handle_safe_msg src dst st msg
    else match cur_request st with
         | Some (query_dst, q, _) =>
           if is_request msg
           then handle_query_req_busy src dst st msg
           else handle_query_res src dst st query_dst q msg
         | None =>
           if is_request msg
           then match handle_query_req st msg with
                | Some p => (st, [(src, p)], [], [])
                | None => (st, [], [], [])
                end
           else (st, [], [], [])
         end.

  Definition pi {A B C D : Type} (t : A * B * C * D) : A * B * C :=
    let '(a, b, c, d) := t in (a, b, c).

  Definition start_handler (h : addr) (knowns : list addr) : data * list (addr * payload) * list timeout :=
    match knowns with
      | k :: [] =>
        let known := make_pointer k in
        let st := Data (make_pointer h) None [] known false None None [] in
        pi (start_query h st (Join known))
      | k :: nowns =>
        let p := make_pointer k in
        let succs := chop_succs (map make_pointer nowns) in
        let st := Data (make_pointer h) (Some p) succs p true None None [] in
        (st, [], [Tick])
      (* garbage data, shouldn't happen *)
      | [] => (Data (make_pointer h) None [] (make_pointer h) false None None [], [], [])
    end.

  Definition tick_handler (h : addr) (st : data) : res :=
    add_tick (match cur_request st with
      | Some _ => (st, [], [], [])
      | None => if joined st
                then start_query h st Stabilize
                else (st, [], [], [])
    end).

  Definition handle_query_timeout (h : addr) (st : data) (dead : pointer) (q : query) : res :=
    match q with
      | Rectify notifier => end_query h (update_pred st notifier, [], [], [])
      | Stabilize =>
        match succ_list st with
          | _ :: rest => start_query h (update_succ_list st rest) Stabilize
          | [] => end_query h (st, [], [], []) (* should not happen in a good network (TODO add axiom?) *)
        end
      | Stabilize2 new_succ =>
        match succ_list st with
          | next :: _ => end_query h (st, [(addr_of next, Notify)], [], [])
          | [] => end_query h (st, [], [], []) (* again, this shouldn't happen (TODO prove this) *)
        end
      | Join known => end_query h (st, [], [], [])
      | Join2 new_succ => end_query h (st, [], [], [])
    end.

  Definition send_keepalives (st : data) : list (addr * payload) :=
    map (fun q => (fst q, Busy)) (delayed_queries st).

  Definition timeout_handler (h : addr) (st : data) (t : timeout) : res :=
    match t with
      | Request dst msg =>
        match cur_request st with
          | Some (ptr, q, _) => if addr_eq_dec (addr_of ptr) dst
                                then handle_query_timeout h st ptr q
                                else (st, [], [], []) (* shouldn't happen *)
          | None => (st, [], [], []) (* shouldn't happen (TODO prove this) *)
        end
      | Tick => tick_handler h st
      | KeepaliveTick => (st, send_keepalives st, [KeepaliveTick], [])
    end.
End Chord.
