Require Import Verdi.
Require Import StateMachineHandlerMonad.

Require Import String.
Require Import StringMap.

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

Theorem output_eq_dec : forall x y: output, {x = y} + {x <> y}.
Proof.
  decide equality;
  auto using key_eq_dec, value_eq_dec, val_eq_dec.
Defined.

Definition data :=
  StringTree.t string.

Definition beq_key (k1 k2 : key) :=
  if string_dec k1 k2 then true else false.

Definition getk k : GenHandler1 data (option value) :=
  db <- get ;;
  ret (StringTree.get k db).

Definition setk k v : GenHandler1 data unit := modify (fun db => StringTree.set k v db).

Definition delk k : GenHandler1 data unit := modify (fun db => StringTree.remove k db).

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
    init := StringTree.empty string ;
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
                                   (StringTree.get (input_key i) st) = (v, o) ->
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
    find_rewrite_lem StringTree.gempty. auto.
Qed.

Definition trace_state_correct (trace : list (input * output)) (st : data) (st' : data) :=
  forall k,
    fst (interpret k (rev (inputs_with_key trace k)) (StringTree.get k st)) = StringTree.get k st'.

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

Theorem step_1_star_trace_state_correct :
  forall st st' trace,
    step_1_star st st' trace ->
    trace_state_correct trace st st'.
Proof.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  induction H; auto.
  - unfold trace_state_correct. auto.
  - unfold trace_state_correct in *. intros.
    invcs H0. unfold VarDHandler, VarDHandler' in *.
    vard_unfold. repeat break_match; simpl in *; repeat find_inversion.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        subst. symmetry; apply StringTree.gss.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite StringTree.gso; auto.
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
        symmetry; apply StringTree.grs.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite StringTree.gro; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * subst. rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        break_if; eauto using StringTree.gss.
        exfalso. intuition.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite StringTree.gso; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * rewrite inputs_with_key_plus_key; simpl in *; auto.
        rewrite rev_unit. simpl in *.
        subst. break_if; eauto using StringTree.grs.
        subst.
        exfalso. intuition.
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
    + simpl in *.
      destruct (key_eq_dec k0 k).
      * { subst. rewrite inputs_with_key_plus_key; simpl in *; auto.
          rewrite rev_unit. simpl in *.
          break_if; simpl in *.
          - symmetry. apply StringTree.grs.
          - exfalso. intuition.
            match goal with
              | H : _ -> False |- _ => apply H
            end.
            find_higher_order_rewrite. auto.
        }
      * rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
        rewrite StringTree.gro; eauto.
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
    step_1_star st st' trace ->
    trace_correct' st trace.
Proof.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  induction H.
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
