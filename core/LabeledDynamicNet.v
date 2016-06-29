Require Import List.
Require Import Arith.
Import ListNotations.
Require Import infseq.

Section LabeledDynamic.
  Variable addr : Type. (* must be finite, decidable *)
  Variable addr_eq_dec : forall x y : addr, {x = y} + {x <> y}.
  Variable payload : Type. (* must be serializable *)
  Variable payload_eq_dec : forall x y : payload, {x = y} + {x <> y}.
  Variable data : Type.
  Variable timeout : Type.
  Variable timeout_eq_dec : forall x y : timeout, {x = y} + {x <> y}.
  Variable label : Type.
  Variable label_eq_dec : forall x y : label, {x = y} + {x <> y}.

  Variable start_handler : addr -> list addr -> data * list (addr * payload) * list timeout.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Variable recv_handler : addr -> addr -> data -> payload -> (res * label).
  Variable timeout_handler : addr -> data -> timeout -> (res * label).

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

  Inductive labeled_step_dynamic : global_state -> label -> global_state -> Prop :=
  | LTimeout :
      forall gst gst' h st t lb st' ms newts clearedts,
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some st ->
        In t (timeouts gst h) ->
        timeout_handler h st t = (st', ms, newts, clearedts, lb) ->
        gst' = (apply_handler_result
                  h
                  (st', ms, newts, t :: clearedts)
                  (e_timeout h t)
                  gst) ->
        extra_constraints gst' ->
        labeled_step_dynamic gst lb gst'
  | LDeliver_node :
      forall gst gst' m h d xs ys ms lb st newts clearedts,
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some d ->
        recv_handler (fst m) h d (snd (snd m)) = (st, ms, newts, clearedts, lb) ->
        gst' = apply_handler_result
                 h
                 (st, ms, newts, clearedts)
                 (e_recv m)
                 (update_msgs gst (xs ++ ys)) ->
        extra_constraints gst' ->
        labeled_step_dynamic gst lb gst'.

Record occurrence := { occ_gst : global_state ; occ_label : label }.

Definition enabled (l : label) (gst : global_state) : Prop :=
  exists gst', labeled_step_dynamic gst l gst'.

Definition l_enabled (l : label) (occ : occurrence) : Prop :=
  enabled l (occ_gst occ).

Definition occurred (l : label) (occ :occurrence) : Prop := l = occ_label occ.

Definition inf_enabled (l : label) (s : infseq occurrence) : Prop :=
  inf_often (now (l_enabled l)) s.

Definition inf_occurred (l : label) (s : infseq occurrence) : Prop :=
  inf_often (now (occurred l)) s.

Definition strong_local_fairness (s : infseq occurrence) : Prop :=
  forall l : label, inf_enabled l s -> inf_occurred l s.

Lemma strong_local_fairness_invar :
  forall e s, strong_local_fairness (Cons e s) -> strong_local_fairness s.
Proof. 
  unfold strong_local_fairness. unfold inf_enabled, inf_occurred, inf_often. 
  intros e s fair a alev. 
  assert (alevt_es: always (eventually (now (l_enabled a))) (Cons e s)).
  constructor. 
  constructor 2. destruct alev; assumption. 
  simpl. assumption.
  clear alev. generalize (fair a alevt_es); clear fair alevt_es.
  intro fair; case (always_Cons fair); trivial.
Qed.

CoInductive lb_execution : infseq occurrence -> Prop :=
  Cons_lb_exec : forall (o o' : occurrence) (s : infseq occurrence),
    labeled_step_dynamic (occ_gst o) (occ_label o) (occ_gst o') ->
    lb_execution (Cons o' s) ->
    lb_execution (Cons o (Cons o' s)).

Lemma lb_execution_invar :
  forall x s, lb_execution (Cons x s) -> lb_execution s.
Proof.
  intros x s e. change (lb_execution (tl (Cons x s))).
  destruct e; simpl. assumption. 
Qed.

End LabeledDynamic.
