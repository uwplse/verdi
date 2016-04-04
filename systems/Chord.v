Require Import Arith.
Require Import List.
Import ListNotations.

Definition addr := nat.
Definition addr_eq_dec := Nat.eq_dec.
Definition id := nat.
Definition pointer := (id * addr)%type.
Definition id_of (p : pointer) : id := fst p.
Definition addr_of (p : pointer) : addr := snd p.
Definition SUCC_LIST_LEN := 5.
Definition pointer_eq_dec : forall x y : pointer, {x = y} + {x <> y}.
Proof.
  decide equality; auto using Nat.eq_dec.
Defined.
Definition N := 256.
Definition make_pointer (a : addr) : pointer := (a mod N, a).

Inductive payload :=
| GetBestPredecessor : addr -> payload
| GotBestPredecessor : pointer -> payload
| GetSuccList : payload
| GotSuccList : list pointer -> payload
| GetPredAndSuccs : payload
| GotPredAndSuccs : option pointer -> list pointer -> payload
| Notify : payload
| Ping : payload
| Pong : payload.

Definition client_payload p := exists (a: addr), p = GetBestPredecessor a.
Definition request_payload p := (exists (a : addr), p = GetBestPredecessor a)
                                                 \/ p = GetSuccList
                                                 \/ p = GetPredAndSuccs
                                                 \/ p = Ping.

Definition is_request (p : payload) :=
  match p with
    | GetBestPredecessor _ => true
    | GetSuccList => true
    | GetPredAndSuccs => true
    | Ping => true
    | _ => false
  end.

Definition can_be_client (a : addr) := True.
Definition can_be_node (a : addr) := True.

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
                      cur_request : option (pointer * query) ;
                      query_sent : bool }.

Definition update_pred (st : data) (p : pointer) := Data (ptr st) (Some p) (succ_list st) (known st) (joined st) (rectify_with st) (cur_request st) (query_sent st).

Definition update_succ_list (st : data) (succs : list pointer) := Data (ptr st) (pred st) succs (known st) (joined st) (rectify_with st) (cur_request st) (query_sent st).

Definition update_query (st : data) (dst : pointer) (q : query) := Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) (Some (dst, q)) (query_sent st).

Definition update_for_join (st : data) (succs : list pointer) := Data (ptr st) None succs (known st) true (rectify_with st) (cur_request st) (query_sent st).


Definition set_rectify_with (st : data) (rw : pointer) :=
  Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (Some rw) (cur_request st) (query_sent st).

Definition clear_rectify_with (st : data) :=
  Data (ptr st) (pred st) (succ_list st) (known st) (joined st) None (cur_request st) (query_sent st).

Definition make_request (h : addr) (st : data) (k : query) : option (pointer * payload) :=
    match k with
    | Rectify notifier => match pred st with
                          | Some p => Some (p, Ping)
                          | None => None
                          end
    | Stabilize => match head (succ_list st) with
                   | Some succ => Some (succ, GetPredAndSuccs)
                   | None => None (* should not happen in a good network *)
                   end
    | Stabilize2 new_succ => Some (new_succ, GetSuccList)
    | Join known => Some (known, GetBestPredecessor h)
    | Join2 new_succ => Some (new_succ, GetSuccList)
    end.

Definition start_query (h : addr) (st : data) (k : query) : data * list (addr * payload) :=
  match make_request h st k with
  | Some (dst, msg) => (update_query st dst k, [(addr_of dst, msg)])
  | None => (st, []) (* should not happen *)
  end.

(* something to prove: try_rectify is not invoked unless cur_request st is None *)
Definition try_rectify (h : addr) (outs : list (addr * payload)) (st : data) : data * list (addr * payload) :=
  if joined st
  then match rectify_with st with
         | Some new => match pred st with
                         | Some _ => let st' := clear_rectify_with st in
                                     start_query h st' (Rectify new)
                         | None => let st' := clear_rectify_with (update_pred st new) in
                                   (st', outs)
                       end
         | None => (st, outs)
       end
  else (st, outs).

Definition request_in (msgs : list (addr * payload)) :=
  existsb is_request (map snd msgs).

Definition end_query (h : addr) (outs : list (addr * payload)) (st : data) : data * list (addr * payload) :=
  let st' := Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) None false in
  match outs with
    | [] => try_rectify h outs st
    | head :: rest => if request_in (head :: rest)
                      then (st, outs)
                      else try_rectify h outs st
  end.

Definition ptrs_to_addrs : list (pointer * payload) -> list (addr * payload) :=
  map (fun p => (addr_of (fst p), (snd p))).

(* true iff n in (a, b) on some sufficiently large "circle" *)
Definition between_bool (a : nat) (x : nat) (b : nat) : bool :=
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

Definition make_succs (head : pointer) (rest : list pointer) : list pointer :=
  firstn SUCC_LIST_LEN (head :: rest).

Definition best_predecessor (h : addr) (st : data) (id : addr) : pointer :=
  let splits (s : pointer) : bool := between_bool h (addr_of s) id
  in match head (filter splits (rev (succ_list st))) with
     | Some succ => succ
     | None => ptr st
     end.

Definition handle_rectify (h : addr) (st : data) (my_pred : pointer) (q : query) (notifier : pointer) : data * list (addr * payload) :=
  if between_bool (id_of my_pred) (id_of notifier) (id_of (ptr st))
  then (update_pred st notifier, [])
  else (st, []).

Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : pointer) (succs : list pointer) : data * list (addr * payload) :=
  let new_st := update_succ_list st (make_succs src succs) in
    if between_bool (id_of (ptr st)) (id_of new_succ) (id_of src)
    then start_query h new_st (Stabilize2 new_succ)
    else (new_st, [(addr_of src, Notify)]).

Definition handle_query (src : addr) (h : addr) (st : data) (qdst : pointer) (q : query) (msg : payload) : data * list (addr * payload) :=
  match q with
    | Rectify notifier =>
      match msg with
        | Pong => match (pred st) with
                    | Some p => handle_rectify h st p q notifier
                    | None => (st, [])
                  end
        | _ => (st, [])
      end
    | Stabilize =>
      match msg with
        | GotPredAndSuccs new_succ succs =>
          match new_succ with
            | Some ns => handle_stabilize h (make_pointer src) st q ns succs
            (* this should never happen *)
            | None => (st, [])
          end
        | _ => (st, [])
      end
    | Stabilize2 new_succ =>
      match msg with
        | GotSuccList succs => (update_succ_list st (make_succs new_succ succs), [])
        | _ => (st, [])
      end
    | Join known =>
      match msg with
        | GotBestPredecessor p => let a := addr_of p in
                                  if pointer_eq_dec p qdst
                                  then (st, [(a, GetSuccList)])
                                  else (st, [(a, GetBestPredecessor h)])
        | GotSuccList l =>
          match l with
            | [] => (st, []) (* this is bad *)
            | (new_succ :: _) => start_query (addr_of new_succ) st (Join2 new_succ)
          end
        | _ => (st, [])
      end
    | Join2 new_succ =>
      match msg with
        | GotSuccList l => let succs := make_succs new_succ l in
                           (update_for_join st succs, [])
        | _ => (st, [])
      end
  end.

Definition recv_handler (src : addr) (dst : addr) (msg : payload) (st : data) : data * list (addr * payload) :=
  match msg with
  | Ping => (st, [(src, Pong)])
  | GetSuccList => (st, [(src, GotSuccList (succ_list st))])
  | GetPredAndSuccs => (st, [(src, GotPredAndSuccs (pred st) (succ_list st))])
  | GetBestPredecessor id => (st, [(src, GotBestPredecessor (best_predecessor dst st id))])
  | Notify => (set_rectify_with st (make_pointer src), [])
  | _ => match cur_request st with
         | Some (query_dst, q) => if addr_eq_dec (addr_of query_dst) src
                     then let (st', outs) := handle_query src dst st query_dst q msg in
                          end_query dst outs st'
                     else (st, [])
         | None => (st, [])
         end
  end.

Definition start_handler (h : addr) (knowns : list addr) : data * list (addr * payload) :=
  match knowns with
    | k :: _ =>
      let known := make_pointer k in
      let st := Data (make_pointer h) None [] known false None None false in
      start_query h st (Join known)
    (* garbage data, shouldn't happen *)
    | [] => (Data (make_pointer h) None [] (make_pointer h) false None None false, [])
  end.

Definition tick_handler (h : addr) (st : data) : data * list (addr * payload) :=
  match cur_request st with
    | Some _ => (st, [])
    | None => if joined st
              then start_query h st Stabilize
              else start_query h st (Join (known st))
  end.

Definition handle_query_timeout (h : addr) (st : data) (dead : pointer) (q : query) : data * list (addr * payload) :=
  match q with
    | Rectify notifier => (update_pred st notifier, [])
    | Stabilize =>
      match succ_list st with
        | _ :: rest => start_query h (update_succ_list st rest) Stabilize
        | [] => (st, []) (* should not happen in a good network *)
      end
    | Stabilize2 new_succ =>
      match succ_list st with
        | next :: _ => (st, [(addr_of next, Notify)])
        | [] => (st, []) (* again, this shouldn't happen *)
      end
    | Join known => (st, []) (* should step to next in the knowns list somehow *)
    | Join2 new_succ => (st, []) (* ditto as for join *)
  end.

Definition timeout_handler (src : addr) (dst : addr) (st : data) : data * list (addr * payload) :=
  match cur_request st with
    | Some (ptr, q) => if pointer_eq_dec ptr (make_pointer dst)
                       then let (st', outs) := handle_query_timeout src st ptr q in
                            end_query src outs st'
                       else (st, []) (* shouldn't happen *)
    | None => (st, []) (* shouldn't happen *)
 end.