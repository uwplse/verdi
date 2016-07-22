Require Import Arith.
Require Import List.
Import ListNotations.

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
                        cur_request : option (pointer * query * payload) }.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Definition client_payload msg := exists (p : pointer), msg = GetBestPredecessor p.

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

  Definition update_pred (st : data) (p : pointer) := Data (ptr st) (Some p) (succ_list st) (known st) (joined st) (rectify_with st) (cur_request st).

  Definition update_succ_list (st : data) (succs : list pointer) := Data (ptr st) (pred st) succs (known st) (joined st) (rectify_with st) (cur_request st).

  Definition update_query (st : data) (dst : pointer) (q : query) (m : payload) := Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) (Some (dst, q, m)).

  Definition update_for_join (st : data) (succs : list pointer) := Data (ptr st) None succs (known st) true (rectify_with st) (cur_request st).

  Definition set_rectify_with (st : data) (rw : pointer) :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (Some rw) (cur_request st).

  Definition clear_rectify_with (st : data) :=
    Data (ptr st) (pred st) (succ_list st) (known st) (joined st) None (cur_request st).

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

  Definition end_query (h : addr) (r : res) : res :=
    let '(st, outs, nts, cts) := r in
    let st' := Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) None in
    let clearreq := timeouts_in st in
    if request_in outs
    then (st', outs, nts, cts ++ clearreq)
    else try_rectify h (st', outs, nts, cts).

  Definition ptrs_to_addrs : list (pointer * payload) -> list (addr * payload) :=
    map (fun p => (addr_of (fst p), (snd p))).

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

  Definition chop_succs (succs : list pointer) : list pointer :=
    firstn SUCC_LIST_LEN succs.

  Definition make_succs (head : pointer) (rest : list pointer) : list pointer :=
    chop_succs (head :: rest).

  Definition best_predecessor (h : pointer) (succs : list pointer) (id : id) : pointer :=
    let splits (s : pointer) : bool := between_bool (id_of h) (id_of s) id
    in match head (filter splits (rev succs)) with
         | Some succ => succ
         | None => h
       end.

  Definition handle_rectify (h : addr) (st : data) (my_pred : pointer) (q : query) (notifier : pointer) : res :=
    if between_bool (id_of my_pred) (id_of notifier) (id_of (ptr st))
    then (update_pred st notifier, [], [], [])
    else (st, [], [], []).

  Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : pointer) (succs : list pointer) : res :=
    let new_st := update_succ_list st (make_succs src succs) in
    if between_bool (id_of (ptr st)) (id_of new_succ) (id_of src)
    then start_query h new_st (Stabilize2 new_succ)
    else end_query h (new_st, [(addr_of src, Notify)], [], []).

  Definition handle_query (src : addr) (h : addr) (st : data) (qdst : pointer) (q : query) (msg : payload) : res :=
    match q with
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

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    match msg with
      | Ping => (st, [(src, Pong)], [], [])
      | GetSuccList => (st, [(src, GotSuccList (succ_list st))], [], [])
      | GetPredAndSuccs => (st, [(src, GotPredAndSuccs (pred st) (succ_list st))], [], [])
      | GetBestPredecessor p => (st, [(src, GotBestPredecessor (best_predecessor (ptr st) (succ_list st) (id_of p)))], [], [])
      | Notify => (set_rectify_with st (make_pointer src), [], [], [])
      | _ => match cur_request st with
               | Some (query_dst, q, _) => handle_query src dst st query_dst q msg
               | None => (st, [], [], [])
             end
    end.

  Definition pi {A B C D : Type} (t : A * B * C * D) : A * B * C :=
    let '(a, b, c, d) := t in (a, b, c).

  Definition start_handler (h : addr) (knowns : list addr) : data * list (addr * payload) * list timeout :=
    match knowns with
      | k :: [] =>
        let known := make_pointer k in
        let st := Data (make_pointer h) None [] known false None None in
        pi (start_query h st (Join known))
      | k :: nowns =>
        let p := make_pointer k in
        let succs := chop_succs (map make_pointer nowns) in
        let st := Data (make_pointer h) (Some p) succs p true None None in
        (st, [], [Tick])
      (* garbage data, shouldn't happen *)
      | [] => (Data (make_pointer h) None [] (make_pointer h) false None None, [], [])
    end.

  Definition tick_handler (h : addr) (st : data) : res :=
    add_tick (match cur_request st with
      | Some _ => (st, [], [], [])
      | None => if joined st
                then start_query h st Stabilize
                else (st, [], [], []) (*start_query h st (Join (known st))*)
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
    end.
End Chord.