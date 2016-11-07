Require Import List.
Require Import Arith.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import StructTact.RemoveAll.
Require Import InfSeqExt.infseq.
Import ListNotations.

Section Dynamic.
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

  Variable recv_handler : addr -> addr -> data -> payload -> res.
  Variable timeout_handler : addr -> data -> timeout -> res.
  Variable recv_handler_l : addr -> addr -> data -> payload -> (res * label).
  Variable timeout_handler_l : addr -> data -> timeout -> (res * label).

  Variable recv_handler_labeling :
    forall src dst st p r,
      (recv_handler src dst st p = r ->
       exists l,
         recv_handler_l src dst st p = (r, l)) /\
      (forall l,
          recv_handler_l src dst st p = (r, l) ->
          recv_handler src dst st p = r).

  Variable timeout_handler_labeling :
    forall h st t r,
      (timeout_handler h st t = r ->
      exists l,
        timeout_handler_l h st t = (r, l)) /\
      (forall l,
          timeout_handler_l h st t = (r, l) ->
          timeout_handler h st t = r).

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

  Variable timeout_constraint : global_state -> addr -> timeout -> Prop.
  (* failure_constraint is parametrized over an initial state, the
     address of the failing node, and what the state would be after
     the failure. *)
  Variable failure_constraint : global_state -> addr -> global_state -> Prop.

  Definition nil_state : addr -> option data := fun _ => None.
  Definition nil_timeouts : addr -> list timeout := fun _ => [].
  Definition init :=
    {| nodes := []; failed_nodes := []; timeouts := nil_timeouts; sigma := nil_state; msgs := []; trace := [] |}.

  Definition clear_timeouts (ts : list timeout) (cts : list timeout) : list timeout :=
    remove_all timeout_eq_dec cts ts.

  Definition update_msgs (gst : global_state) (ms : list msg) : global_state :=
    {| nodes := nodes gst;
       failed_nodes := failed_nodes gst;
       timeouts := timeouts gst;
       sigma := sigma gst;
       msgs := ms;
       trace := trace gst
    |}.

  Definition fail_node (gst : global_state) (h : addr) : global_state :=
    {| nodes := nodes gst;
       failed_nodes := h :: failed_nodes gst;
       timeouts := timeouts gst;
       sigma := sigma gst;
       msgs := msgs gst;
       trace := trace gst
    |}.

  Definition apply_handler_result (h : addr) (r : res) (es : list event) (gst : global_state) : global_state :=
    let '(st, ms, nts, cts) := r in
    let sends := map (send h) ms in
    let ts' := nts ++ clear_timeouts (timeouts gst h) cts in
    {| nodes := nodes gst;
       failed_nodes := failed_nodes gst;
       timeouts := update addr_eq_dec (timeouts gst) h ts';
       sigma := update addr_eq_dec (sigma gst) h (Some st);
       msgs := sends ++ msgs gst;
       trace := trace gst ++ es
    |}.

  Lemma apply_handler_result_nodes :
    forall h r e gst,
      nodes (apply_handler_result h r e gst) = nodes gst.
  Proof.
    unfold apply_handler_result.
    intros.
    now repeat break_let.
  Qed.

  Definition update_for_start
             (gst : global_state) (h : addr)
             (res : data * list (addr * payload) * list timeout) : global_state :=
    let '(st, ms, newts) := res in
    let sends := map (send h) ms in
    {| nodes := h :: nodes gst;
       failed_nodes := failed_nodes gst;
       timeouts := update addr_eq_dec (timeouts gst) h newts;
       sigma := update addr_eq_dec (sigma gst) h (Some st);
       msgs := sends ++ msgs gst;
       trace := trace gst ++ (map e_send sends)
    |}.

  Lemma update_for_start_nodes :
    forall gst gst' h res,
      update_for_start gst h res = gst' ->
      h :: nodes gst = nodes gst'.
  Proof.
    unfold update_for_start.
    intros.
    repeat break_let.
    now repeat find_reverse_rewrite.
  Qed.

  Lemma update_for_start_nodes_eq :
    forall gst h res,
      nodes (update_for_start gst h res) = h :: nodes gst.
  Proof.
    unfold update_for_start.
    intros.
    now repeat break_let.
  Qed.

  Lemma update_for_start_sigma_h_exists :
    forall gst h res,
      exists st,
        sigma (update_for_start gst h res) h = Some st.
  Proof.
    unfold update_for_start.
    intros.
    repeat break_let.
    simpl.
    eexists; eauto using update_eq.
  Qed.

  Lemma update_for_start_sigma_h_n :
    forall gst h n res st,
      h <> n ->
      sigma gst n = Some st ->
      sigma (update_for_start gst h res) n = Some st.
  Proof.
    unfold update_for_start.
    intros.
    repeat break_let.
    simpl.
    now rewrite update_diff.
  Qed.

  Inductive step_dynamic : global_state -> global_state -> Prop :=
  | Start :
      forall h gst gst' k,
        ~ In h (nodes gst) ->
        (* hypotheses on the list of known nodes *)
        In k (nodes gst) ->
        ~ In k (failed_nodes gst) ->
        (* note that clearedts might as well be [] *)
        gst' = update_for_start gst h (start_handler h (k :: nil)) ->
        step_dynamic gst gst'
  | Fail :
      forall h gst gst',
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        gst' = fail_node gst h ->
        failure_constraint gst h gst' ->
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
                  [e_timeout h t]
                  gst) ->
        timeout_constraint gst h t ->
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
                 [e_recv m]
                 (update_msgs gst (xs ++ ys)) ->
        step_dynamic gst gst'.

  Inductive labeled_step_dynamic : global_state -> label -> global_state -> Prop :=
  | LTimeout :
      forall gst gst' h st t lb st' ms newts clearedts,
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some st ->
        In t (timeouts gst h) ->
        timeout_handler_l h st t = (st', ms, newts, clearedts, lb) ->
        gst' = (apply_handler_result
                  h
                  (st', ms, newts, t :: clearedts)
                  [e_timeout h t]
                  gst) ->
        timeout_constraint gst h t ->
        labeled_step_dynamic gst lb gst'
  | LDeliver_node :
      forall gst gst' m h d xs ys ms lb st newts clearedts,
        msgs gst = xs ++ m :: ys ->
        h = fst (snd m) ->
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        sigma gst h = Some d ->
        recv_handler_l (fst m) h d (snd (snd m)) = (st, ms, newts, clearedts, lb) ->
        gst' = apply_handler_result
                 h
                 (st, ms, newts, clearedts)
                 [e_recv m]
                 (update_msgs gst (xs ++ ys)) ->
        labeled_step_dynamic gst lb gst'.

  Record occurrence := { occ_gst : global_state ; occ_label : label }.

  Definition enabled (l : label) (gst : global_state) : Prop :=
    exists gst', labeled_step_dynamic gst l gst'.

  Definition l_enabled (l : label) (occ : occurrence) : Prop :=
    enabled l (occ_gst occ).

  Definition occurred (l : label) (occ :occurrence) : Prop := l = occ_label occ.

  Definition inf_enabled (l : label) (s : infseq occurrence) : Prop :=
    inf_often (now (l_enabled l)) s.

  Definition cont_enabled (l : label) (s : infseq occurrence) : Prop :=
    continuously (now (l_enabled l)) s.

  Definition inf_occurred (l : label) (s : infseq occurrence) : Prop :=
    inf_often (now (occurred l)) s.

  Definition strong_local_fairness (s : infseq occurrence) : Prop :=
    forall l : label, inf_enabled l s -> inf_occurred l s.

  Definition weak_local_fairness (s : infseq occurrence) : Prop :=
    forall l : label, cont_enabled l s -> inf_occurred l s.

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

  Lemma weak_local_fairness_invar :
    forall e s, weak_local_fairness (Cons e s) -> weak_local_fairness s.
  Proof.
    unfold weak_local_fairness. unfold cont_enabled, inf_occurred, continuously, inf_often.
    intros e s fair l eval.
    assert (eval_es: eventually (always (now (l_enabled l))) (Cons e s)).
      apply E_next. assumption.
    apply fair in eval_es.
    apply always_invar in eval_es.
    assumption.
  Qed.

  Lemma strong_local_fairness_weak :
    forall s, strong_local_fairness s -> weak_local_fairness s.
  Proof.
  intros [e s].
  unfold strong_local_fairness, weak_local_fairness, inf_enabled, cont_enabled.
  intros H_str l H_cont.
  apply H_str.
  apply continuously_inf_often.
  assumption.
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

  Lemma labeled_step_is_unlabeled_step :
    forall gst l gst',
      labeled_step_dynamic gst l gst' ->
      step_dynamic gst gst'.
  Proof.
    intuition.
    match goal with
      | H: labeled_step_dynamic _ _ _ |- _ =>
        invc H
    end.
    - find_apply_lem_hyp timeout_handler_labeling.
      eauto using Timeout, timeout_handler_labeling.
    - find_apply_lem_hyp recv_handler_labeling.
      eauto using Deliver_node.
  Qed.

  Inductive churn_between (gst gst' : global_state) : Prop :=
    | fail_churn : failed_nodes gst <> failed_nodes gst' -> churn_between gst gst'
    | join_churn : nodes gst <> nodes gst' -> churn_between gst gst'.

  Ltac invc_lstep :=
    match goal with
      | H: labeled_step_dynamic _ _ _ |- _ =>
        invc H
    end.

  Lemma list_neq_cons :
    forall A (l : list A) x,
      x :: l <> l.
  Proof.
    intuition.
    symmetry in H.
    induction l;
      now inversion H.
  Qed.

  Lemma labeled_step_dynamic_is_step_dynamic_without_churn :
    forall gst gst',
      step_dynamic gst gst' ->
      ((exists l, labeled_step_dynamic gst l gst') /\ ~ churn_between gst gst') \/
      ((~ exists l, labeled_step_dynamic gst l gst') /\ churn_between gst gst').
  Proof.
    intuition.
    match goal with
      | H: step_dynamic _ _ |- _ =>
        invc H
    end.
    - right.
      split.
      * intuition.
        break_exists.
        invc_lstep;
          find_apply_lem_hyp update_for_start_nodes;
          find_rewrite_lem apply_handler_result_nodes;
          eapply list_neq_cons; eauto.
      * apply join_churn.
        rewrite update_for_start_nodes_eq.
        eauto using list_neq_cons.
    - right.
      unfold fail_node.
      split.
      * intuition.
        break_exists.
        invc_lstep;
          unfold apply_handler_result in *;
          find_inversion;
          eapply list_neq_cons;
          eauto.
      * eauto using fail_churn, list_neq_cons.
    - left.
      split.
      * find_apply_lem_hyp timeout_handler_labeling.
        break_exists_exists.
        eauto using LTimeout.
      * intuition.
        match goal with
        | H: churn_between _ _ |- _ =>
          inversion H; eauto
        end.
    - left.
      split.
      * find_apply_lem_hyp recv_handler_labeling.
        break_exists_exists.
        eauto using LDeliver_node.
      * intuition.
        match goal with
        | H: churn_between _ _ |- _ =>
          inversion H; eauto
        end.
  Qed.

End Dynamic.
