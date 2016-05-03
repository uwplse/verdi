Require Import DynamicNet.
Require Import Chord.
Require Import List.
Require Import Arith.

Section ChordProof.
  Variable SUCC_LIST_LEN : nat.
  Variable hash : addr -> id.
  Variable hash_inj : forall a b : addr,
      hash a = hash b -> a = b.
  Variable base : list addr.
  Variable base_size : length base = SUCC_LIST_LEN + 1.

  Notation start_handler := (start_handler SUCC_LIST_LEN hash).
  Notation recv_handler := (recv_handler SUCC_LIST_LEN hash).
  Notation timeout_handler := (timeout_handler hash).

  Notation global_state := (global_state addr payload data timeout).
  Notation nodes := (nodes addr payload data timeout).
  Notation failed_nodes := (failed_nodes addr payload data timeout).
  Notation sigma := (sigma addr payload data timeout).

  Notation step_dynamic := (step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec start_handler recv_handler timeout_handler client_payload can_be_client can_be_node).

  Notation e_timeout := (e_timeout addr payload timeout).
  Notation e_fail := (e_fail addr payload timeout).

  Axiom timeouts_detect_failure : forall trace xs ys t h dead req,
      trace = xs ++ t :: ys ->
      (* if a request timeout occurs at some point in the trace... *)
      t = (e_timeout h (Request dead req)) ->
      (* then it corresponds to an earlier node failure. *)
      In (e_fail dead) xs.

  (* tip: treat this as opaque and use lemmas: it never gets stopped except by failure *)
  Definition live_node (gst : global_state) (h : addr) : Prop := forall st,
    sigma gst h = Some st ->
    joined st = true /\
    In h (nodes gst) /\
    ~ In h (failed_nodes gst).

  Definition live_node_dec (gst : global_state) (h : addr) :=
    match sigma gst h with
      | Some st => if joined st
                   then if in_dec addr_eq_dec h (nodes gst)
                        then if in_dec addr_eq_dec h (failed_nodes gst)
                             then false
                             else true
                        else false
                   else false
      | None => false
    end.

  Definition best_succ (gst : global_state) (h s : addr) : Prop :=
    forall st o, exists xs ys,
      sigma gst h = Some st ->
      map addr_of (succ_list st) = xs ++ s :: ys ->
      (In o xs -> ~ live_node gst o) /\
      live_node gst s.

  (* transitive closure of best_succ *)
  (* treat as opaque *)
  Inductive reachable (gst : global_state) : addr -> addr -> Prop :=
    | ReachableSucc : forall from to,
        best_succ gst from to ->
        reachable gst from to
    | ReachableTransL : forall from x to,
        best_succ gst from x ->
        reachable gst x to ->
        reachable gst from to.
  (* prove the other direction is available *)

  Definition best_succ_of (gst : global_state) (h : addr) : option addr :=
    match (sigma gst) h with
      | Some st => head (filter (live_node_dec gst) (map addr_of (succ_list st)))
      | None => None
    end.

  (* treat as opaque *)
  Definition ring_member (gst : global_state) (h : addr) : Prop :=
    reachable gst h h.

  Definition at_least_one_ring (gst : global_state) : Prop :=
    exists h, ring_member gst h.

  Definition at_most_one_ring (gst : global_state) : Prop :=
    forall x y,
      ring_member gst x ->
      ring_member gst y ->
      reachable gst x y.

  Definition between (x y z : id) :=
    x < y < z \/ y < z < x \/ z < x < y.

  Definition ordered_ring (gst : global_state) : Prop :=
    forall h s x,
      ring_member gst h ->
      best_succ gst h s ->
      ring_member gst x ->
      ~ between h x s. (* TODO fix between semantics *)
      (* or between h x s -> s = x *)

  Definition connected_appendages (gst : global_state) : Prop :=
    forall a, exists r,
      live_node gst a ->
      ring_member gst r /\ reachable gst a r.

  Definition base_not_skipped (gst : global_state) : Prop :=
    forall h b succs xs s ys st,
      live_node gst h ->
      Some st = sigma gst h ->
      succs = map addr_of (succ_list st) ->
      xs ++ s :: ys = succs ->
      In b base ->
      between h b s ->
      In b xs.

  Definition inductive_invariant (gst : global_state) : Prop :=
    at_least_one_ring gst /\
    at_most_one_ring gst /\
    ordered_ring gst /\
    connected_appendages gst /\
    base_not_skipped gst.

End ChordProof.