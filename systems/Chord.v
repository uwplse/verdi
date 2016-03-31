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
                      known : option pointer ;
                      joined : bool ;
                      rectify_with : option pointer ;
                      cur_request : option (pointer * query) ;
                      query_sent : bool }.

Definition update_pred (st : data) (p : pointer) := Data (ptr st) (Some p) (succ_list st) (known st) (joined st) (rectify_with st) (cur_request st) (query_sent st).

Definition update_succ_list (st : data) (succs : list pointer) := Data (ptr st) (pred st) succs (known st) (joined st) (rectify_with st) (cur_request st) (query_sent st).

Definition update_query (st : data) (dst : pointer) (q : query) := Data (ptr st) (pred st) (succ_list st) (known st) (joined st) (rectify_with st) (Some (dst, q)) (query_sent st).

Definition update_for_join (st : data) (succs : list pointer) := Data (ptr st) None succs (known st) true (rectify_with st) (cur_request st) (query_sent st).

Definition make_request (h : addr) (st : data) (k : query) : option (pointer * payload) :=
    match k with
    | Rectify notifier => match pred st with
                          | Some p => Some (p, Ping)
                          | None => None
                          end
    | Stabilize => match head (succ_list st) with
                   | Some succ => Some (succ, GetPredAndSuccs)
                   | None => None
                   end
    | Stabilize2 new_succ => Some (new_succ, GetSuccList)
    | Join known => Some (known, GetBestPredecessor h)
    | Join2 new_succ => Some (new_succ, GetSuccList)
    end.

Definition ptrs_to_addrs : list (pointer * payload) -> list (addr * payload) :=
  map (fun p => (addr_of (fst p), (snd p))).
  
Definition start_query (h : addr) (st : data) (k : query) : list (addr * payload) * data :=
  match make_request h st k with
  | Some (dst, msg) => ([(addr_of dst, msg)], update_query st dst k)
  | None => ([], st) (* should not happen *)
  end.

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

Definition handle_rectify (h : addr) (st : data) (my_pred : pointer) (q : query) (notifier : pointer) : list (addr * payload) * data :=
  if between_bool (id_of my_pred) (id_of notifier) (id_of (ptr st))
  then ([], update_pred st notifier)
  else ([], st).

Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : pointer) (succs : list pointer) : list (addr * payload) * data :=
  let new_st := update_succ_list st (make_succs src succs) in
    if between_bool (id_of (ptr st)) (id_of new_succ) (id_of src)
    then start_query h new_st (Stabilize2 new_succ)
    else ([(addr_of src, Notify)], new_st).

Definition handle_query (src : addr) (h : addr) (st : data) (qdst : pointer) (q : query) (msg : payload) : list (addr * payload) * data :=
  match q with
    | Rectify notifier =>
      match msg with
        | Pong => match (pred st) with
                    | Some p => handle_rectify h st p q notifier
                    | None => ([], st)
                  end
        | _ => ([], st)
      end
    | Stabilize =>
      match msg with
        | GotPredAndSuccs new_succ succs =>
          match new_succ with
            | Some ns => handle_stabilize h (make_pointer src) st q ns succs
            (* this should never happen *)
            | None => ([], st)
          end
        | _ => ([], st)
      end
    | Stabilize2 new_succ =>
      match msg with
        | GotSuccList succs => ([], update_succ_list st (make_succs new_succ succs))
        | _ => ([], st)
      end
    | Join known =>
      match msg with
        | GotBestPredecessor p => let a := addr_of p in
                                  if pointer_eq_dec p qdst
                                  then ([(a, GetSuccList)], st)
                                  else ([(a, GetBestPredecessor h)], st)
        | GotSuccList l =>
          match l with
            | [] => ([], st) (* this is bad *)
            | (new_succ :: _) => start_query (addr_of new_succ) st (Join2 new_succ)
          end
        | _ => ([], st)
      end
    | Join2 new_succ =>
      match msg with
        | GotSuccList l => let succs := make_succs new_succ l in
                           ([], update_for_join st succs)
        | _ => ([], st)
      end
  end.

Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : list (addr * payload) * data :=
  match msg with
  | Ping => ([(src, Pong)], st)
  | GetSuccList => ([(src, GotSuccList (succ_list st))], st)
  | GetPredAndSuccs => ([(src, GotPredAndSuccs (pred st) (succ_list st))], st)
  | GetBestPredecessor id => ([(src, GotBestPredecessor (best_predecessor dst st id))], st)
  | _ => match cur_request st with
         | Some (query_dst, q) => if addr_eq_dec (addr_of query_dst) src
                     then handle_query src dst st query_dst q msg
                     else ([], st)
         | None => ([], st)
         end
  end.