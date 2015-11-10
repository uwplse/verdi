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

    (* data for a given node *)
    Record data := mkData { succ : addr;
                           succ2 : addr;
                           pred : addr;
                           bestsucc : addr }.

    Inductive payload :=
    (* join event *)
    | FindSucc : addr -> payload
    | FoundSucc : addr -> payload
    (* stabilize event *)
    | LookupYourPred : payload
    | FoundMyPred : addr -> payload
    (* notify event *)
    | NotifySucc : payload.

    Definition find_succ_handler (src : addr) (dst : addr) (st : data) (asker : addr) : (addr * payload) :=
      if between dst ((succ st) + 1) asker
        then (asker, FoundSucc (succ st))
        else (pred st, FindSucc asker).

    Definition stabilize_handler (src : addr) (dst : addr) (st : data) (p : addr) : list (addr * payload) * data :=
      if between dst (succ st) p
        then ([(p, NotifySucc)], (mkData p (succ st) (pred st) (bestsucc st)))
        else ([((succ st), NotifySucc)], st).
    
    Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : list (addr * payload) * data :=
      match msg with
      | FindSucc addr => ([(find_succ_handler src dst st addr)], st)
      (* how can I change just one field of a record? *)
      | FoundSucc s => ([(s, LookupYourPred)], (mkData s (succ2 st) (pred st) (bestsucc st)))
      | LookupYourPred => ([(src, FoundMyPred (pred st))], st)
      | FoundMyPred p => stabilize_handler src dst st p
      | NotifySucc => (nil, if between (pred st) dst src then mkData (succ st) (succ2 st) src (bestsucc st) else st)
      end.

End Chord.