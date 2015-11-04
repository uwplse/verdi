Require Import List.
Import ListNotations.


Section Dynamic.
  Variable addr : Type. (* must be finite, decidable *)
  Variable addr_eq_dec : forall x y : addr, {x = y} + {x <> y}.
  Variable payload : Type. (* must be serializable *)
  Variable data : Type.
  Variable start_handler : addr -> list (addr * payload) * data.
  Variable recv_handler : addr -> addr -> data -> payload -> list (addr * payload) * data.
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
  | e_recv : msg -> event.
  
  Record global_state :=
    { nodes : list addr;
      sigma : addr -> option data;
      msgs : list msg;
      trace : list event
    }.

  Definition nil_state : addr -> option data := fun _ => None.
  Definition init :=
    {| nodes := []; sigma := nil_state; msgs := []; trace := [] |}.
  
  Definition update (f : addr -> option data) (a : addr) (d : data) (a' : addr) :=
    if addr_eq_dec a a' then Some d else f a'.

  Notation "f [ a '=>' d ]" := (update f a d) (at level 0).

  (* no failures for now but easy to add *)
  Inductive step_dynamic : global_state -> global_state -> Prop :=
  | Start :
      forall h gst ms st new_msgs,
        can_be_node h ->
        ~ In h (nodes gst) ->
        start_handler h = (ms, st) ->
        new_msgs = map (send h) ms ->
        step_dynamic gst {| nodes := h :: nodes gst;
                            sigma := (sigma gst)[h => st];
                            msgs := new_msgs ++ msgs gst;
                            trace := trace gst ++ (map e_send new_msgs)
                         |}
  | Deliver_client :
      forall gst m h xs ys,
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        ~ In h (nodes gst) ->
        step_dynamic gst {| nodes := nodes gst;
                            sigma := sigma gst;
                            msgs := xs ++ ys;
                            trace := trace gst ++ [e_recv m]
                         |}
  | Deliver_node :
      forall gst m h d xs ys ms st,
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        In h (nodes gst) ->
        sigma gst h = Some d ->
        recv_handler h (fst m) d (snd (snd m)) = (ms, st) ->
        step_dynamic gst {| nodes := nodes gst;
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
                            sigma := sigma gst;
                            msgs := m :: (msgs gst);
                            trace := trace gst ++ [e_send m]
                         |}.
End Dynamic.
