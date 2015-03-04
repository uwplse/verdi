Require Import Arith.
Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.

Require Import Net.

Require Import String.

Definition key := string.
Definition value := string.

Inductive input : Set :=
| Put : key -> value -> input
| Get : key -> input
| Del : key -> input
| CAS : key -> option value -> value -> input
| CAD : key -> value -> input.

Inductive output : Set :=
| Response : key -> option value -> option value -> output (* uniform response *)
.

Definition key_eq_dec := string_dec.
Definition value_eq_dec := string_dec.

Definition val_eq_dec : forall v v' : option value, {v = v'} + {v <> v'}.
  decide equality.
  auto using value_eq_dec.
Defined.

Theorem input_eq_dec : forall x y: input, {x = y} + {x <> y}.
Proof.
  decide equality;
  auto using key_eq_dec, value_eq_dec, val_eq_dec.
Defined.

Theorem output_eq_dec : forall x y: input, {x = y} + {x <> y}.
Proof.
  decide equality;
  auto using key_eq_dec, value_eq_dec, val_eq_dec.
Defined.

Definition data :=
  list (key * value) %type.

Definition beq_key (k1 k2 : key) :=
  if string_dec k1 k2 then true else false.

Section assoc.
  Variable K V : Type.
  Variable K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}.

  Fixpoint assoc (l : list (K * V)) (k : K) : option V :=
    match l with
      | [] => None
      | (k', v) :: l' =>
        if K_eq_dec k k' then
          Some v
        else
          assoc l' k
    end.

  Fixpoint assoc_set (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
    match l with
      | [] => [(k, v)]
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          (k, v) :: l'
        else
          (k', v') :: (assoc_set l' k v)
    end.

  Fixpoint assoc_del (l : list (K * V)) (k : K) : list (K * V) :=
    match l with
      | [] => []
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          l'
        else
          (k', v') :: (assoc_del l' k)
    end.

  Lemma get_set_same :
    forall k v l,
      assoc (assoc_set l k v) k = Some v.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; congruence.
  Qed.

  Lemma get_set_diff :
    forall k k' v l,
      k <> k' ->
      assoc (assoc_set l k v) k' = assoc l k'.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma not_in_assoc :
    forall k l,
      ~ In k (map (@fst _ _) l) ->
      assoc l k = None.
  Proof.
    intros.
    induction l.
    - auto.
    - simpl in *. repeat break_match; intuition.
      subst. simpl in *. congruence.
  Qed.

  Lemma get_del_same :
    forall k l,
      NoDup (map (@fst _ _) l) ->
      assoc (assoc_del l k) k = None.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - invc H.
      repeat break_match; subst.
      + simpl in *. apply not_in_assoc. auto.
      + simpl in *. break_if; try congruence.
        auto.
  Qed.

  Lemma get_del_diff :
    forall k k' l,
      k <> k' ->
      assoc (assoc_del l k') k = assoc l k.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat (break_match; simpl); subst; try congruence.
      auto.
  Qed.
End assoc.

Arguments assoc {_} {_} _ _ _.
Arguments assoc_set {_} {_} _ _ _ _.
Arguments assoc_del {_} {_} _ _ _.
Require Import StateMachineHandlerMonad.
Definition getk k : GenHandler1 data (option value) :=
  db <- get ;;
  ret (assoc key_eq_dec db k).

Definition setk k v : GenHandler1 data unit := modify (fun db => assoc_set key_eq_dec db k v).

Definition delk k : GenHandler1 data unit := modify (fun db => assoc_del key_eq_dec db k).

Definition resp k v old : GenHandler1 data output :=
  write_output (Response k v old).

Definition VarDHandler' (inp : input) : GenHandler1 data output :=
  match inp with
    | Get k => v <- getk k ;; resp k v v
    | Put k v => old <- getk k ;; setk k v ;; resp k (Some v) old
    | Del k => old <- getk k ;; delk k ;; resp k None old
    | CAS k v v' =>
      old <- getk k ;;
          if (val_eq_dec old v) then
            (setk k v' ;; resp k (Some v') old)
          else
            resp k old old
    | CAD k v =>
      old <- getk k ;;
          if (val_eq_dec old (Some v)) then
            (delk k ;; resp k None old)
          else
            resp k old old
  end.

Definition runHandler (h : input -> GenHandler1 data output)
           (inp : input) (d : data) : output * data :=
  runGenHandler1 d (h inp).

Definition VarDHandler := runHandler VarDHandler'.

Instance vard_base_params : BaseParams :=
  {
    data := data ;
    input := input ;
    output := output
  }.

Instance vard_one_node_params : OneNodeParams _ :=
  {
    init := [] ;
    handler := VarDHandler
  }.

Definition input_key (i : input) : key :=
  match i with
    | Get k => k
    | Put k _ => k
    | Del k => k
    | CAS k _ _ => k
    | CAD k _ => k
  end.

Definition operate (op : input) (curr : option value) :=
  match op with
    | Get _ => (curr, curr)
    | Put _ v => (Some v, curr)
    | Del _ => (None, curr)
    | CAS _ v v' => if val_eq_dec curr v then (Some v', curr) else (curr, curr)
    | CAD _ v => if val_eq_dec curr (Some v) then (None, curr) else (curr, curr)
  end.

Fixpoint interpret (k : key) (ops : list input) (init : option value) :=
  match ops with
    | [] => (init, init)
    | op :: ops =>
      (operate op (fst (interpret k ops init)))
  end.

Definition inputs_with_key (trace : list (input * output)) (k : key) : list input :=
  filterMap (fun ev => if key_eq_dec k (input_key (fst ev)) then
                            Some (fst ev)
                          else
                            None)
            trace.


Inductive trace_correct : list (input * output) -> Prop :=
| TCnil : trace_correct []
| TCApp : forall t i v o, trace_correct t ->
                     interpret (input_key i)
                               (i :: (rev (inputs_with_key t (input_key i))))
                               None = (v, o) ->
                     trace_correct (t ++ [(i, Response (input_key i) v o)]).

Inductive trace_correct' : data -> list (input * output) -> Prop :=
| TC'nil : forall st, trace_correct' st []
| TC'App : forall st t i v o, trace_correct' st t ->
                         interpret (input_key i)
                                   (i :: (rev (inputs_with_key t (input_key i))))
                                   (assoc key_eq_dec st (input_key i)) = (v, o) ->
                         trace_correct' st (t ++ [(i, Response (input_key i) v o)]).

Lemma trace_correct'_trace_correct :
  forall trace,
    trace_correct' init trace ->
    trace_correct trace.
Proof.
  intros.
  remember init as x. induction H.
  - constructor.
  - subst. constructor; auto.
Qed.

Definition trace_state_correct (trace : list (input * output)) (st : data) (st' : data) :=
  forall k,
    fst (interpret k (rev (inputs_with_key trace k)) (assoc key_eq_dec st k)) = assoc key_eq_dec st' k.

Ltac vard_unfold :=
  unfold runHandler,
  getk,
  setk,
  delk,
  resp in *; monad_unfold.

Lemma trace_well_formed :
  forall st st' trace,
    step_1_star st st' trace ->
    (trace = [] \/ exists t i o, trace = t ++ [(i, o)]).
Proof.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  invcs H; intuition.
  right. exists cs. invcs H1. unfold VarDHandler, VarDHandler' in *.
  vard_unfold.
  repeat break_match; simpl in *; repeat find_inversion; repeat eexists; eauto.
Qed.

Lemma inputs_with_key_plus_key :
  forall l k i o,
    input_key i = k ->
    inputs_with_key (l ++ [(i, o)]) k =
    (inputs_with_key l k) ++ [i].
Proof.
  induction l; intros; simpl in *.
  - unfold inputs_with_key. simpl in *.
    repeat break_match; congruence.
  - unfold inputs_with_key in *.
    simpl in *.
    repeat break_match; simpl in *; f_equal; eauto.
Qed.

Lemma inputs_with_key_plus_not_key :
  forall l k i o,
    input_key i <> k ->
    inputs_with_key (l ++ [(i, o)]) k =
    (inputs_with_key l k).
Proof.
  induction l; intros; simpl in *.
  - unfold inputs_with_key. simpl in *.
    repeat break_match; congruence.
  - unfold inputs_with_key in *.
    simpl in *.
    repeat break_match; simpl in *; eauto; try discriminate.
    repeat find_inversion.
    f_equal. eauto.
Qed.

Definition no_dup_keys (d : data) :=
  NoDup (map (fst (B:=value)) d).

Lemma assoc_set_in_diff_key :
  forall K V st K_eq_dec (k : K) k' (v : V),
    k <> k' ->
    In k (map (fst (B:=V)) (assoc_set K_eq_dec st k' v)) ->
    In k (map (fst (B:=V)) st).
Proof.
  induction st; intros; simpl in *; intuition.
  repeat break_match; subst; in_crush.
  right. eapply IHst; eauto using in_map.
Qed.

Lemma assoc_del_in_diff_key :
  forall K V st K_eq_dec (k : K) k',
    k <> k' ->
    In k (map (fst (B:=V)) (assoc_del K_eq_dec st k')) ->
    In k (map (fst (B:=V)) st).
Proof.
  induction st; intros; simpl in *; intuition.
  repeat break_match; subst; in_crush.
  right. eapply IHst; eauto using in_map.
Qed.

Lemma assoc_set_preserves_NoDup :
  forall K V st K_eq_dec (k : K) (v : V),
    NoDup (map (fst (B:=V)) st) ->
    NoDup (map (fst (B:=V)) (assoc_set K_eq_dec st k v)).
Proof.
  induction st; intros; simpl in *.
  - constructor; intuition.
  - repeat break_match.
    + subst; auto.
    + subst. simpl in *.
      invcs H.
      constructor.
      * intuition.
        eauto using assoc_set_in_diff_key.
      * eauto.
Qed.

Lemma assoc_del_preserves_NoDup :
  forall K V st K_eq_dec (k : K),
    NoDup (map (fst (B:=V)) st) ->
    NoDup (map (fst (B:=V)) (assoc_del K_eq_dec st k)).
Proof.
  induction st; intros; simpl in *.
  - constructor; intuition.
  - repeat break_match.
    + subst; auto.
      simpl in *. invcs H. auto.
    + subst. simpl in *.
      invcs H.
      constructor.
      * intuition.
        eauto using assoc_del_in_diff_key.
      * eauto.
Qed.

Lemma no_dup_keys_invariant :
  forall st st' trace,
    step_1_star st st' trace ->
    no_dup_keys st ->
    no_dup_keys st'.
Proof.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  induction H; auto. invcs H1; intuition.
  unfold VarDHandler, VarDHandler' in *.
  vard_unfold.
  repeat break_match; simpl in *; repeat find_inversion; unfold no_dup_keys in *;
  eauto using assoc_set_preserves_NoDup, assoc_del_preserves_NoDup.
Qed.

Theorem step_1_star_trace_state_correct :
  forall st st' trace,
    no_dup_keys st ->
    step_1_star st st' trace ->
    trace_state_correct trace st st'.
Proof.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  induction H0; auto.
  - unfold trace_state_correct. intros.
    simpl in *.  auto.
  - unfold trace_state_correct in *. intros.
    invcs H1. unfold VarDHandler, VarDHandler' in *.
    vard_unfold. repeat break_match; simpl in *; repeat find_inversion.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        subst. symmetry; apply get_set_same.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite get_set_diff; auto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        subst. eauto.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        subst. eauto.
        symmetry; apply get_del_same.
        find_apply_lem_hyp refl_trans_n1_1n_trace.
        find_apply_lem_hyp no_dup_keys_invariant; eauto.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite get_del_diff; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * subst. rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        break_if; eauto using get_set_same.
        exfalso. intuition.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite get_set_diff; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        subst. break_if; eauto using get_del_same.
        subst.
        exfalso. intuition.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * { subst. rewrite inputs_with_key_plus_key; simpl in *; auto.
          rewrite rev_unit. simpl in *.
          break_if; simpl in *.
          - symmetry. apply get_del_same.
            find_apply_lem_hyp refl_trans_n1_1n_trace.
            find_apply_lem_hyp no_dup_keys_invariant; eauto.
          - exfalso. intuition.
            match goal with
              | H : _ -> False |- _ => apply H
            end.
            find_higher_order_rewrite. auto.
        }
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite get_del_diff; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * subst. rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        break_if; simpl in *; intuition.
        exfalso. intuition.
        match goal with
          | H : _ -> False |- _ => apply H
        end.
        find_higher_order_rewrite. auto.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
Qed.

Lemma trace_state_correct_trace_correct :
  forall st st' st'' trace t,
    trace_state_correct trace st st' ->
    trace_correct' st trace ->
    step_1 st' st'' t ->
    trace_correct' st (trace ++ t).
Proof.
  intros.
  invcs H1; simpl in *.
  unfold VarDHandler, VarDHandler' in *.
  vard_unfold.
  repeat break_match; simpl in *; repeat find_inversion; constructor; auto;
  simpl in *; f_equal; eauto;
  break_if; simpl in *;  f_equal; eauto; unfold trace_state_correct in *;
  exfalso; subst; repeat find_higher_order_rewrite;
  intuition.
Qed.

Theorem step_1_star_trace_correct' :
  forall st st' trace,
    no_dup_keys st ->
    step_1_star st st' trace ->
    trace_correct' st trace.
Proof.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  induction H0.
  - constructor.
  - find_apply_lem_hyp refl_trans_n1_1n_trace.
    find_apply_lem_hyp step_1_star_trace_state_correct; auto.
    eapply trace_state_correct_trace_correct; eauto.
Qed.

Theorem step_1_star_trace_correct :
  forall st trace,
    step_1_star init st trace ->
    trace_correct trace.
Proof.
  intros.
  find_apply_lem_hyp step_1_star_trace_correct'.
  eauto using trace_correct'_trace_correct.
  unfold no_dup_keys. simpl in *. constructor.
Qed.

Open Scope string_scope.
Example trace_correct_eg0 :
  trace_correct [(Put "james" "awesome", Response "james" (Some "awesome") None)].
Proof.
  rewrite <- app_nil_l.
  constructor.
  - constructor.
  - simpl. auto.
Qed.
