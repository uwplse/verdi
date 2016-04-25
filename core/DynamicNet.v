Require Import List.
Import ListNotations.


Section Dynamic.
  Variable addr : Type. (* must be finite, decidable *)
  Variable addr_eq_dec : forall x y : addr, {x = y} + {x <> y}.
  Variable payload : Type. (* must be serializable *)
  Variable data : Type.
  Variable timeout : Type.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.
  Variable start_handler : addr -> list addr -> res.
  Variable recv_handler : addr -> addr -> data -> payload -> res.
  Variable timeout_handler : addr -> data -> timeout -> res.
  
  (* can clients send this payload? disallows forgery *)
  Variable client_payload : payload -> Prop.

  Variable can_be_client : addr -> Prop.
  Variable can_be_node : addr -> Prop.

  (* msgs *)
  Definition msg := (addr * (addr * payload))%type.
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

  Definition nil_state : addr -> option data := fun _ => None.
  Definition nil_timeouts : addr -> list timeout := fun _ => [].
  Definition init :=
    {| nodes := []; failed_nodes := []; timeouts := nil_timeouts; sigma := nil_state; msgs := []; trace := [] |}.
  
  Definition update (f : addr -> option data) (a : addr) (d : data) (a' : addr) :=
    if addr_eq_dec a a' then Some d else f a'.
  Definition updatets (f : addr -> list timeout) (a : addr) (t : list timeout) (a' : addr) :=
    if addr_eq_dec a a' then t else f a'.
  Notation "f [ a '=>' d ]" := (update f a d) (at level 0).
  Notation "f [ a '==>' d ]" := (updatets f a d) (at level 0).

  Inductive step_dynamic : global_state -> global_state -> Prop :=
  | Start :
      forall h gst ms st new_msgs known k t ts ts' newts clearedts,
        can_be_node h ->
        ~ In h (nodes gst) ->
        (In k known -> In k (nodes gst)) ->
        (In k known -> ~ In k (failed_nodes gst)) ->
        (known = [] -> (nodes gst) = []) ->
        ts = timeouts gst h ->
        (In t clearedts -> In t ts) ->
        (In t ts' -> ~ In t clearedts /\ (In t ts \/ In t newts)) ->
        start_handler h known = (st, ms, newts, clearedts) ->
        new_msgs = map (send h) ms ->
        step_dynamic gst {| nodes := h :: nodes gst;
                            failed_nodes := failed_nodes gst;
                            timeouts := (timeouts gst)[h ==> ts'];
                            sigma := (sigma gst)[h => st];
                            msgs := new_msgs ++ msgs gst;
                            trace := trace gst ++ (map e_send new_msgs)
                         |}
  | Fail :
      forall h gst,
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        step_dynamic gst {| nodes := nodes gst;
                            failed_nodes := h :: (failed_nodes gst);
                            timeouts := timeouts gst;
                            sigma := sigma gst;
                            msgs := msgs gst;
                            trace := trace gst ++ [e_fail h]
                         |}
  | Timeout :
      forall gst h st ts xts t t' yts ts' st' ms newts clearedts,
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some st ->
        xts ++ t :: yts = (timeouts gst h) ->
        ts = xts ++ yts ->
        (In t' clearedts -> In t' ts) ->
        (In t' ts' -> ~ In t' clearedts /\ (In t' ts \/ In t' newts)) ->
        timeout_handler h st t = (st', ms, newts, clearedts) ->
        step_dynamic gst {| nodes := nodes gst;
                            failed_nodes := failed_nodes gst;
                            timeouts := (timeouts gst)[h ==> ts'];
                            sigma := (sigma gst)[h => st'];
                            msgs := map (send h) ms ++ msgs gst;
                            trace := trace gst ++ [e_timeout h t]
                         |}
  | Deliver_client :
      forall gst m h xs ys,
        can_be_client h ->
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        ~ In h (nodes gst) ->
        step_dynamic gst {| nodes := nodes gst;
                            failed_nodes := failed_nodes gst;
                            timeouts := timeouts gst;
                            sigma := sigma gst;
                            msgs := xs ++ ys;
                            trace := trace gst ++ [e_recv m]
                         |}
  | Deliver_node :
      forall gst m h d xs ys ms st ts ts' t newts clearedts,
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some d ->
        (In t clearedts -> In t ts) ->
        (In t ts' -> ~ In t clearedts /\ (In t ts \/ In t newts)) ->
        recv_handler h (fst m) d (snd (snd m)) = (st, ms, newts, clearedts) ->
        step_dynamic gst {| nodes := nodes gst;
                            failed_nodes := failed_nodes gst;
                            timeouts := (timeouts gst)[h ==> ts'];
                            sigma := (sigma gst)[h => st];
                            msgs := map (send h) ms ++ xs ++ ys;
                            trace := trace gst ++ [e_recv m]
                         |}
  | Input :
      forall gst m h to i,
        can_be_client h ->
        client_payload i ->
        ~ In h (nodes gst) ->
        m = send h (to, i) ->
        step_dynamic gst {| nodes := nodes gst;
                            failed_nodes := failed_nodes gst;
                            timeouts := timeouts gst;
                            sigma := sigma gst;
                            msgs := m :: (msgs gst);
                            trace := trace gst ++ [e_send m]
                         |}.
End Dynamic.
