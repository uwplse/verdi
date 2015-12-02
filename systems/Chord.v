Require Import Arith.
Require Import List.
Import ListNotations.

Section Chord.
    Definition addr := nat.
    Definition key := addr.

    (* true iff n in (a, b) on some sufficiently large "circle" *)
    Definition between (a : nat) (b : nat) (n : nat) : bool :=
      match nat_compare a b with
      | Eq => false (* this really shouldn't happen. thanks for reading *)
      (* this seems.. unnecessary? *)
      | Lt => if (gt_dec a n) then if (lt_dec n b) then true else false else false
      | Gt => if (gt_dec n a) then true else if (lt_dec n b) then true else false
      end.

    Inductive liveness :=
      | Unknown : liveness
      | Pinged : liveness
      | Live : liveness
      | Dead : liveness.

    Definition node_pointer := option (addr * liveness).

    (* data for a given node *)
    Record data := mkData { succ : node_pointer;
                           succ2 : node_pointer;
                           pred : node_pointer }.

    Inductive payload :=
    (* join event *)
    | FindSucc : addr -> payload
    | FoundSucc : addr -> payload
    (* stabilize event *)
    | LookupYourPred : payload
    | FoundMyPred : addr -> payload
    (* notify event *)
    | NotifySucc : payload
    (* reconcile event *)
    | LookupYourSucc : payload
    | FoundMySucc : addr -> payload
    (* update and reconcile events *)
    | Ping : payload
    | Pong : payload.

    Definition find_succ_handler (src : addr) (dst : addr) (st : data) (asker : addr) : list (addr * payload) :=
      match succ st with
      | Some (addr, _)  => if between dst (addr + 1) asker
                          then [(asker, FoundSucc addr)]
                          else match pred st with
                               | Some (addr, _) => [(addr, FindSucc asker)]
                               | None => []
                               end
      | None => []
      end.

    Definition stabilize_handler (src : addr) (dst : addr) (st : data) (p : addr) : list (addr * payload) * data :=
      match succ st with
      | Some (addr, l) => if between dst addr p
                    then ([(p, NotifySucc)], (mkData (Some (p, l)) (succ st) (pred st)))
                    else ([(addr, NotifySucc)], st)
      | None => ([], st)
      end.

    Definition pong_handler (p : node_pointer) (src : addr) :=
      match p with
      | Some (addr, Pinged) => if beq_nat addr src then Some (addr, Live) else p
      | _ => p
      end.

    Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : list (addr * payload) * data :=
      match msg with
      | FindSucc addr => ((find_succ_handler src dst st addr), st)
      (* how can I change just one field of a record? *)
      | FoundSucc s => ([(s, LookupYourPred)], (mkData (Some (s, Unknown)) (succ2 st) (pred st)))
      | LookupYourPred => match pred st with
                         | Some (p, Live) => ([(src, FoundMyPred p)], st)
                         | _ => ([], st)
                         end
      | FoundMyPred p => stabilize_handler src dst st p
      | NotifySucc => match pred st with
                     | Some (p, Live) => ([], if between p dst src then mkData (succ st) (succ2 st) (Some (src, Unknown)) else st)
                     | _ => ([], st)
                     end
      | LookupYourSucc => match succ st with
                         | Some (s, Live) => ([(src, FoundMySucc s)], st)
                         | _ => ([], st)
                         end
      | FoundMySucc s => ([], mkData (succ st) (Some (s, Unknown)) (pred st))
      | Ping => ([(src, Pong)], st)
      | Pong => ([], mkData (pong_handler (succ st) src)
                           (pong_handler (succ2 st) src)
                           (pong_handler (pred st) src))
      end.

    Definition do_ping (p : node_pointer) : list (addr * payload) :=
      match p with
      | Some (a, Unknown) => [(a, Ping)]
      | Some (a, Live) => [(a, Ping)]
      | _ => nil
      end.

    Definition do_ping_st (p : node_pointer) : node_pointer :=
      match p with
      | Some (addr, Pinged) => Some (addr, Dead)
      | Some (addr, Unknown) => Some (addr, Pinged)
      | Some (addr, Live) =>   Some (addr, Pinged)
      | _ => p
      end.

    Definition do_pings (st : data) : list (addr * payload) :=
      do_ping (succ st) ++ do_ping (succ2 st) ++ do_ping (pred st).

    Definition do_ping_states (st : data) : data :=
      mkData (do_ping_st (succ st))
             (do_ping_st (succ2 st))
             (do_ping_st (pred st)).

    Definition start_reconcile (st : data) : list (addr * payload) :=
      match succ st with
      | Some (a, Dead) => nil
      | Some (a, _) => [(a, LookupYourSucc)]
      | None => nil
      end.

    Definition do_update (st : data) : data :=
      match succ st with
      | Some (a, Dead) => mkData (succ2 st) None (pred st)
      | _ => st
      end.

    Definition do_flush (st : data) : data :=
      match pred st with
      | Some (a, Dead) => mkData (succ st) (succ2 st) None
      | _ => st
      end.

    Definition timeout_handler (node : addr) (st : data) : list (addr * payload) * data :=
      (start_reconcile st ++ do_pings st,
       (do_flush (do_update (do_ping_states st)))).
End Chord.
