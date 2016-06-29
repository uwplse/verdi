Require Import List.
Require Import Arith.
Import ListNotations.


Section Dynamic.
  Variable addr : Type. (* must be finite, decidable *)
  Variable addr_eq_dec : forall x y : addr, {x = y} + {x <> y}.
  Variable payload : Type. (* must be serializable *)
  Variable payload_eq_dec : forall x y : payload, {x = y} + {x <> y}.
  Variable data : Type.
  Variable timeout : Type.
  Variable timeout_eq_dec : forall x y : timeout, {x = y} + {x <> y}.

  Variable start_handler : addr -> list addr -> data * list (addr * payload) * list timeout.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Variable recv_handler : addr -> addr -> data -> payload -> res.
  Variable timeout_handler : addr -> data -> timeout -> res.

  (* can clients send this payload? disallows forgery *)
  Variable client_payload : payload -> Prop.

  Variable can_be_client : addr -> Prop.
  Variable can_be_node : addr -> Prop.

  (* msgs *)
  Definition msg := (addr * (addr * payload))%type.
  Definition msg_eq_dec : forall x y : msg, {x = y} + {x <> y}.
    decide equality; destruct b, p.
    decide equality; eauto using addr_eq_dec, payload_eq_dec.
  Defined.
  Definition send (a : addr) (p : addr * payload) : msg :=
    (a, p).

  (* traces *)
  Inductive event :=
  | e_send : msg -> event
  | e_recv : msg -> event
  | e_timeout : addr -> timeout -> event
  | e_fail : addr -> event.
 
  Record global_state :=
    { nodes : list addr;
      failed_nodes : list addr;
      timeouts : addr -> list timeout;
      sigma : addr -> option data;
      msgs : list msg;
      trace : list event
    }.

  Definition gpred := global_state -> Prop.
  Definition gpand (P Q : gpred) : gpred := fun gst => P gst /\ Q gst.

  Variable extra_constraints : gpred.

  Definition nil_state : addr -> option data := fun _ => None.
  Definition nil_timeouts : addr -> list timeout := fun _ => [].
  Definition init :=
    {| nodes := []; failed_nodes := []; timeouts := nil_timeouts; sigma := nil_state; msgs := []; trace := [] |}.

  Definition list_minus {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})  (a : list A) (b : list A) : list A :=
    fold_left (fun acc b => remove eq_dec b acc) b a.

  Definition clear_timeouts (ts : list timeout) (cts : list timeout) : list timeout :=
    list_minus timeout_eq_dec ts cts.

  Definition update (f : addr -> option data) (a : addr) (d : data) (a' : addr) :=
    if addr_eq_dec a a' then Some d else f a'.
  Definition updatets (f : addr -> list timeout) (a : addr) (t : list timeout) (a' : addr) :=
    if addr_eq_dec a a' then t else f a'.
  Notation "f [ a '=>' d ]" := (update f a d) (at level 0).
  Notation "f [ a '==>' d ]" := (updatets f a d) (at level 0).

  Definition update_msgs (gst : global_state) (ms : list msg) : global_state :=
    {| nodes := nodes gst;
       failed_nodes := failed_nodes gst;
       timeouts := timeouts gst;
       sigma := sigma gst;
       msgs := ms;
       trace := trace gst
    |}.

  Definition apply_handler_result (h : addr) (r : res) (e : event) (gst : global_state) : global_state :=
    let '(st, ms, nts, cts) := r in
    let sends := map (send h) ms in
    let ts' := nts ++ clear_timeouts (timeouts gst h) cts in
    {| nodes := nodes gst;
       failed_nodes := failed_nodes gst;
       timeouts := (timeouts gst)[h ==> ts'];
       sigma := (sigma gst)[h => st];
       msgs := sends ++ msgs gst;
       trace := trace gst ++ [e]
    |}.

  Inductive step_dynamic : global_state -> global_state -> Prop :=
  | Start :
      forall h gst gst' ms st new_msgs known k newts,
        can_be_node h ->
        ~ In h (nodes gst) ->
        (* hypotheses on the list of known nodes *)
        (In k known -> In k (nodes gst)) ->
        (In k known -> ~ In k (failed_nodes gst)) ->
        (known = [] -> (nodes gst) = []) ->
        (* note that clearedts might as well be [] *)
        start_handler h known = (st, ms, newts) ->
        new_msgs = map (send h) ms ->
        gst' = {| nodes := h :: nodes gst;
                  failed_nodes := failed_nodes gst;
                  timeouts := (timeouts gst)[h ==> newts];
                  sigma := (sigma gst)[h => st];
                  msgs := new_msgs ++ msgs gst;
                  trace := trace gst ++ (map e_send new_msgs)
               |} ->
        extra_constraints gst' ->
        step_dynamic gst gst'
  | Fail :
      forall h gst gst',
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        gst' = {| nodes := nodes gst;
                  failed_nodes := h :: (failed_nodes gst);
                  timeouts := timeouts gst;
                  sigma := sigma gst;
                  msgs := msgs gst;
                  trace := trace gst ++ [e_fail h]
               |} ->
        extra_constraints gst' ->
        step_dynamic gst gst'
  | Timeout :
      forall gst gst' h st t st' ms newts clearedts,
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
        extra_constraints gst' ->
        step_dynamic gst gst'
  | Deliver_client :
      forall gst gst' m h xs ys,
        can_be_client h ->
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        ~ In h (nodes gst) ->
        gst' = {| nodes := nodes gst;
                  failed_nodes := failed_nodes gst;
                  timeouts := timeouts gst;
                  sigma := sigma gst;
                  msgs := xs ++ ys;
                  trace := trace gst ++ [e_recv m]
               |} ->
        extra_constraints gst' ->
        step_dynamic gst gst'
  | Deliver_node :
      forall gst gst' m h d xs ys ms st newts clearedts,
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some d ->
        recv_handler (fst m) h d (snd (snd m)) = (st, ms, newts, clearedts) ->
        gst' = apply_handler_result
                 h
                 (st, ms, newts, clearedts)
                 (e_recv m)
                 (update_msgs gst (xs ++ ys)) ->
        extra_constraints gst' ->
        step_dynamic gst gst'
  | Input :
      forall gst gst' m h to i,
        can_be_client h ->
        client_payload i ->
        ~ In h (nodes gst) ->
        m = send h (to, i) ->
        gst' = {| nodes := nodes gst;
                  failed_nodes := failed_nodes gst;
                  timeouts := timeouts gst;
                  sigma := sigma gst;
                  msgs := m :: (msgs gst);
                  trace := trace gst ++ [e_send m]
               |} ->
        extra_constraints gst' ->
        step_dynamic gst gst'.
End Dynamic.
