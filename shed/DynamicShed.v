Require Import List.
Import ListNotations.

Require Import DynamicNet.
Require Import Shed.
Require Import StructTact.Update.

Section DynamicShed.
  Variable addr payload data timeout : Type.
  Notation msg := (msg addr payload).
  Notation send := (send addr payload).
  Notation global_state := (global_state addr payload data timeout).
  Notation nodes := (nodes addr payload data timeout).
  Notation failed_nodes := (failed_nodes addr payload data timeout).
  Notation timeouts := (timeouts addr payload data timeout).
  Notation sigma := (sigma addr payload data timeout).
  Notation msgs := (msgs addr payload data timeout).
  Notation trace := (trace addr payload data timeout).
  Notation update_msgs := (update_msgs addr payload data timeout).
  Notation e_send := (e_send addr payload timeout).
  Notation e_recv := (e_recv addr payload timeout).
  Notation e_fail := (e_fail addr payload timeout).
  Notation e_timeout := (e_timeout addr payload timeout).
  Notation fail_node := (fail_node addr payload data timeout).
  Variable addr_eq_dec : forall x y : addr, {x = y} + {x <> y}.
  Variable payload_eq_dec : forall x y : payload, {x = y} + {x <> y}.
  Notation msg_eq_dec := (msg_eq_dec addr addr_eq_dec payload payload_eq_dec).
  Variable timeout_eq_dec : forall x y : timeout, {x = y} + {x <> y}.
  Notation apply_handler_result := (apply_handler_result addr addr_eq_dec payload data timeout timeout_eq_dec).
  Variable start_handler : addr -> list addr -> data * list (addr * payload) * list timeout.
  Variable recv_handler : addr -> addr -> data -> payload -> res addr payload data timeout.
  Variable timeout_handler : addr -> data -> timeout -> res addr payload data timeout.
  Variable timeout_constraint : global_state -> addr -> timeout -> Prop.
  Variable timeout_constraint_dec : forall gst h t,
      {timeout_constraint gst h t} + {~ timeout_constraint gst h t}.
  Variable failure_constraint : global_state -> Prop.
  Variable failure_constraint_dec : forall gst,
      {failure_constraint gst} + {~ failure_constraint gst}.
  Notation step_dynamic := (step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec start_handler recv_handler timeout_handler timeout_constraint failure_constraint).
  Inductive operation :=
  | op_start : addr -> list addr -> operation
  | op_fail : addr -> operation
  | op_timeout : addr * timeout -> operation
  (* the nat here is the index of the msg in (msgs gst) *)
  | op_deliver : nat -> msg -> operation.

  Definition exists_and_not_failed (gst : global_state) (h : addr) : bool :=
    if In_dec addr_eq_dec h (nodes gst)
    then if In_dec addr_eq_dec h (failed_nodes gst)
         then false
         else true
    else false.

  Definition run_start_handler (gst : global_state) (h : addr) (knowns : list addr) : global_state :=
    let '(st, ms, nts) := start_handler h knowns in
    let new_msgs := map (send h) ms in
    {| DynamicNet.nodes := h :: nodes gst;
       DynamicNet.failed_nodes := failed_nodes gst;
       DynamicNet.timeouts := update addr_eq_dec (timeouts gst) h nts;
       DynamicNet.sigma := update addr_eq_dec (sigma gst) h (Some st);
       DynamicNet.msgs := new_msgs ++ msgs gst;
       DynamicNet.trace := trace gst ++ (map e_send new_msgs) |}.

  Definition run_start (gst : global_state) (h : addr) (knowns : list addr) : option global_state :=
    if In_dec addr_eq_dec h (nodes gst)
    then None
    else if forallb (exists_and_not_failed gst) knowns
         then Some (run_start_handler gst h knowns)
         else None.

  Definition run_fail (gst : global_state) (h : addr) :=
    let gst' := fail_node gst h in
    if exists_and_not_failed gst h
    then Some gst' (*if failure_constraint_dec gst'
         then Some gst'
         else None*)
    else None.

  Definition run_timeout_handler (gst : global_state) (h : addr) (st : data) (t : timeout) : global_state :=
    let '(st', ms, nts, cts) := timeout_handler h st t in
    apply_handler_result h (st', ms, nts, t :: cts) (e_timeout h t) gst.

  Definition run_timeout (gst : global_state) (h : addr) (t : timeout) : option global_state :=
    if exists_and_not_failed gst h
    then match sigma gst h with
         | Some st =>
           if In_dec timeout_eq_dec t (timeouts gst h)
           then if timeout_constraint_dec gst h t
                then Some (run_timeout_handler gst h st t)
                else None
           else None
         | None => None
         end
    else None.

  Definition run_recv_handler (gst : global_state) (net : list msg) (src dst : addr) (st : data) (p : payload) : global_state :=
    let '(st', ms, nts, cts) := recv_handler src dst st p in
    apply_handler_result dst (st', ms, nts, cts) (e_recv (src, (dst, p))) (update_msgs gst net).

  Definition selectnth {A : Type} (n : nat) (l : list A) : option (list A * A * list A) :=
    match nth_error l n with
    | Some x => Some (firstn n l, x, skipn (n + 1) l)
    | None => None
    end.

  Definition run_deliver (gst : global_state) (n : nat) (m : msg) : option global_state :=
    match selectnth n (msgs gst) with
    | Some (xs, (dst, (src, p)), ys) =>
      if msg_eq_dec (dst, (src, p)) m
      then if exists_and_not_failed gst dst
           then match sigma gst dst with
                | Some st => Some (run_recv_handler gst (xs ++ ys) src dst st p)
                | None => None
                end
           else None
      else None
    | None => None
    end.

  Definition run (gst : global_state) (op : operation) : option global_state :=
    match op with
    | op_start h knowns => run_start gst h knowns
    | op_fail h => run_fail gst h
    | op_timeout (h, t) => run_timeout gst h t
    | op_deliver n m => run_deliver gst n m
    end.

  Lemma run_valid :
    forall gst op gst',
      run gst op = Some gst' ->
      step_dynamic gst gst'.
  Admitted.

  Lemma run_complete :
    forall gst gst',
      step_dynamic gst gst' ->
      exists op,
        run gst op = Some gst'.
  Admitted.

  Definition possible_starts (gst : global_state) : list operation :=
    [].

  Definition possible_fails (gst : global_state) : list operation :=
    map op_fail (filter (exists_and_not_failed gst) (nodes gst)).

  Definition possible_timeouts_at (gst : global_state) (h : addr) : list operation :=
    map (fun t => op_timeout (h, t)) (timeouts gst h).

  Definition possible_timeouts (gst : global_state) : list operation :=
    concat (map (possible_timeouts_at gst) (filter (exists_and_not_failed gst) (nodes gst))).

  Definition possible_delivers (gst : global_state) : list operation :=
    [].

End DynamicShed.
