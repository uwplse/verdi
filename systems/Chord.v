Require Import Arith.
Require Import List.
Import ListNotations.

Definition addr := nat.
Definition id := nat.
Definition addr_dec := Nat.eq_dec.
Definition pointer := (id * addr)%type.
Definition id_of (p : pointer) : id := fst p.
Definition addr_of (p : pointer) : addr := snd p.
Definition SUCC_LIST_LEN := 5.

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

Inductive query_kind :=
(* needs a pointer to the notifier *)
| Rectify : pointer -> query_kind
| Stabilize : query_kind
(* needs a new successor *)
| Stabilize2 : pointer -> query_kind
(* needs a known node *)
| Join : pointer -> query_kind
(* needs a node (pointer) to ask for the successor of an id *)
| LookupSucc : pointer -> id -> query_kind
(* ditto *)
| LookupPredecessor : pointer -> id -> query_kind
(* needs a node to get the successor of*)
| GetSucc : pointer -> query_kind
(* needs to know new successor *)
| Join2 : pointer -> query_kind.

Record query := Query { query_dst : pointer ;
                        msg : payload ;
                        kind : query_kind }.

Record data := Data { ptr : pointer ;
                      pred : option pointer ;
                      succ_list : list pointer ;
                      known : option pointer ;
                      joined : bool ;
                      rectify_with : option pointer ;
                      cur_query : option query ;
                      query_sent : bool }.

Definition update_pred (st : data) (p : pointer) := Data (ptr st) (Some p) (succ_list st) (known st) (joined st) (rectify_with st) (cur_query st) (query_sent st).

Definition make_request (h : addr) (st : data) (k : query_kind) : option (pointer * payload) :=
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
    | LookupSucc host id => Some (host, GetBestPredecessor id)
    | LookupPredecessor host id => Some (host, GetBestPredecessor id)
    | GetSucc ptr => Some (ptr, GetSuccList)
    | Join2 new_succ => Some (new_succ, GetSuccList)
    end.

Definition make_query (h : addr) (st : data) (k : query_kind) : option query :=
    match make_request h st k with
    | Some (d, m) => Some (Query d m k)
    | None => None
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

Definition handle_query (h : addr) (st : data) (q : query) (msg : payload) : list (addr * payload) * data :=
  match kind q with
  | Rectify notifier => match msg with
                        | Pong => match (pred st) with
                                  | Some p => handle_rectify h st p q notifier
                                  | None => ([], st)
                                  end
                        | _ => ([], st)
                        end
  | _ => ([], st)
  end.

Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : list (addr * payload) * data :=
  match msg with
  | Ping => ([(src, Pong)], st)
  | GetSuccList => ([(src, GotSuccList (succ_list st))], st)
  | GetPredAndSuccs => ([(src, GotPredAndSuccs (pred st) (succ_list st))], st)
  | GetBestPredecessor id => ([(src, GotBestPredecessor (best_predecessor dst st id))], st)
  | _ => match cur_query st with
         | Some q => if addr_dec (addr_of (query_dst q)) src then handle_query dst st q msg else ([], st)
         | None => ([], st)
         end
  end.


Definition timeout_handler (node : addr) (st : data) : list (addr * payload) * data := ([], st).