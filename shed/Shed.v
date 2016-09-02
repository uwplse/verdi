Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import String.
Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Require Import Coqlib.
Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.

Section Shed.
  (* The global state type. *)
  Variable net : Type.
  (* Relation defining whether one state can transition to another. *)
  Variable step : net -> net -> Prop.
  (* If steps are lengths of fence, operations are fenceposts. *)
  Variable operation : Type.
  (* You can "run" an operation on a net gst to produce another net
     gst', provided the operation is valid to apply on that net, i.e.,
     step gst gst' holds.

     For example, an operation that crashes a node h won't be valid if
     h isn't a live node. *)
  Variable run : net -> operation -> option net.
  (*
  Variable run_valid :
    forall gst op gst',
      run gst op = Some gst' ->
      step gst gst'.
  Variable run_complete :
    forall gst gst',
      step gst gst' ->
      exists op,
        run gst op = Some gst'.*)

  Definition run_lifted (gst : option net) (o : operation) : option net :=
    match gst with
    | Some gst' => run gst' o
    | None => None
    end.

  (* Runs a list of operations starting at init. Only returns None if
     one of the operations is invalid. *)
  Definition run_all (ops : list operation) (init : net) : option net :=
    fold_left run_lifted ops (Some init).

  Definition valid_operation (gst : net) (op : operation) : Prop :=
    exists gst',
      run gst op = Some gst'.

  (* A netpred is a decidable predicate on nets with a name. *)
  Record netpred := { np_prop : net -> Prop;
                      np_dec : forall gst, {np_prop gst} + {~ np_prop gst};
                      np_name : string }.


  Definition const_true {A} (_ : A) : Prop :=
    True.

  (* a sample netpred *)
  Definition const_true_net_dec :
    forall (gst : net),
      {const_true gst} + {~ const_true gst}.
  Proof.
    intro gst.
    now left.
  Qed.

  Definition np_const_true := {| np_prop := const_true;
                                 np_dec := const_true_net_dec;
                                 np_name := "np_const_true" |}.

  (* Trace predicates are properties of infinite sequences, so we
     can't actually test them. Instead we define a sort of decidable
     version of a trace predicate that maps a finite list of
     occurrences into the tp_result type. *)
  Inductive tp_result : Set :=
  | tp_True   (* I know for sure that it's true *)
  | tp_False  (* I know for sure that it's false *)
  | tp_Maybe. (* I need more information. *)

  Definition tp_result_eq_dec :
    forall (p q : tp_result),
      {p = q} + {p <> q}.
  Proof.
    decide equality.
  Defined.

  (* prefix l s holds when s starts with the elements of l. *)
  Inductive prefix {A} : list A -> infseq A -> Prop :=
  | prefix_nil : forall s,
      prefix [] s
  | prefix_cons : forall x l s,
      prefix l s ->
      prefix (x :: l) (Cons x s).

  Record occurrence := { occ_net : net;
                         occ_op : operation }.
  Definition occ_step (o o' : occurrence) : Prop :=
    run (occ_net o) (occ_op o) = Some (occ_net o').

  Inductive execution_prefix : list occurrence -> Prop :=
  | ep_nil : execution_prefix []
  | ep_one : forall o,
      valid_operation (occ_net o) (occ_op o) ->
      execution_prefix [o]
  | ep_cons : forall l o o',
      execution_prefix (o' :: l) -> 
      occ_step o o' ->
      execution_prefix (o :: o' :: l).

  CoInductive execution : infseq occurrence -> Prop := 
    exec_Cons : forall o o' s,
      occ_step o o' ->
      execution (Cons o' s) ->
      execution (Cons o (Cons o' s)).

  Definition tp_True_correct (tp_prop : infseq occurrence -> Prop) (tp_dec : list occurrence -> tp_result) (l : list occurrence) : Prop :=
    tp_dec l = tp_True ->
    forall s,
      execution s ->
      prefix l s ->
      tp_prop s.

  Definition tp_False_correct (tp_prop : infseq occurrence -> Prop) (tp_dec : list occurrence -> tp_result) (l : list occurrence) : Prop :=
    tp_dec l = tp_False ->
    forall s,
      execution s ->
      prefix l s ->
      ~ tp_prop s.

  Definition tp_Maybe_correct (tp_prop : infseq occurrence -> Prop) (tp_dec : list occurrence -> tp_result) (l : list occurrence) : Prop :=
    tp_dec l = tp_Maybe ->
    exists s s',
      execution s /\ prefix l s /\ tp_prop s /\
      execution s' /\ prefix l s /\ ~ tp_prop s'.

  (* What it means for a tp_dec to do something *)
  Definition tracepred_correct (tp_prop : infseq occurrence -> Prop) (tp_dec : list occurrence -> tp_result) : Prop :=
    forall l,
      tp_True_correct tp_prop tp_dec l \/
      tp_False_correct tp_prop tp_dec l \/
      tp_Maybe_correct tp_prop tp_dec l.

  (* A tracepred is a predicate on infinite executions with a
     decidable analogue defined on finite executions and a name. *)
  Record tracepred := { tp_prop : infseq occurrence -> Prop;
                        tp_dec : list occurrence -> tp_result;
                        tp_correct : tracepred_correct tp_prop tp_dec;
                        tp_name : string }.

  Definition const_true_tp_dec (t : list occurrence) : tp_result :=
    tp_True.

  Definition const_true_tp_dec_correct :
    tracepred_correct const_true const_true_tp_dec.
  Proof.
    left.
    easy.
  Defined.

  Definition tp_const_true := {| tp_prop := const_true;
                                 tp_dec := const_true_tp_dec;
                                 tp_correct := const_true_tp_dec_correct;
                                 tp_name := "tp_const_true" |}.

  Definition is_tp_false (p : tp_result) : bool :=
    if tp_result_eq_dec p tp_False
    then true
    else false.
  
  Definition any_tracepreds_false (preds : list tracepred) (l : list occurrence) : bool :=
    existsb is_tp_false (map (fun p => tp_dec p l) preds).

  Definition any_netpreds_false (preds : list netpred) (gst : net) : bool :=
    existsb (Bool.eqb false) (map (fun p => proj_sumbool (np_dec p gst)) preds).

  Record test_state := { (* trace of program thus far *)
                         ts_trace : list occurrence; 
                         (* latest state, since occurrences have a sort of fencepost issue *)
                         ts_latest : net;
                         ts_netpreds : list (netpred * list bool); 
                         ts_tracepreds : list (tracepred * list tp_result);
                         ts_error : option string }.

  Definition extend_by (st : test_state) (gst : net) (op : operation) : test_state :=
    {| ts_trace := ts_trace st ++ [{| occ_net := ts_latest st;
                                      occ_op := op |}];
       ts_latest := gst;
       ts_netpreds := ts_netpreds st;
       ts_tracepreds := ts_tracepreds st;
       ts_error := ts_error st |}.

  Definition try_step_test (st : test_state) (op : operation) : option test_state :=
    match run (ts_latest st) op with
    | Some gst' => Some (extend_by st gst' op)
    | None => None
    end.

  Definition update_netpred_result (st : test_state) (npres : netpred * list bool) : netpred * list bool :=
    let (np, results) := npres in
    (np, (proj_sumbool (np_dec np (ts_latest st))) :: results).

  Definition update_netpreds_results (st : test_state) : list (netpred * list bool) :=
    map (update_netpred_result st) (ts_netpreds st).

  Definition update_tracepred_result (st : test_state) (tpres : tracepred * list tp_result) : tracepred * list tp_result :=
    let (tp, results) := tpres in
    (tp, (tp_dec tp (ts_trace st)) :: results).

  Definition update_tracepreds_results (st : test_state) : list (tracepred * list tp_result) :=
    map (update_tracepred_result st) (ts_tracepreds st).

  Definition add_checks_for_latest (st : test_state) : test_state :=
    {| ts_trace := ts_trace st;
       ts_latest := ts_latest st;
       ts_netpreds := update_netpreds_results st;
       ts_tracepreds := update_tracepreds_results st;
       ts_error := ts_error st |}.

  Definition set_error (st : test_state) s :=
    {| ts_trace := ts_trace st;
       ts_latest := ts_latest st;
       ts_netpreds := ts_netpreds st;
       ts_tracepreds := ts_tracepreds st;
       ts_error := Some s |}.

  Fixpoint random_test_body (st : test_state) (next : net -> nat -> operation) (n : nat) : test_state :=
    let st_checked := add_checks_for_latest st in
    match n with
    | O => st
    | S n' =>
      match try_step_test st_checked (next (ts_latest st_checked) n) with
      | Some st' => random_test_body st' next n'
      | None => set_error st "planned an invalid operation"
      end
    end.

  Definition pair_to_nil {A B: Type} (x : A) : A * (list B) :=
    (x, []).

  Definition make_initial_state (init : net) (netpreds : list netpred) (tracepreds : list tracepred) : test_state :=
    {| ts_trace := [];
       ts_latest := init;
       ts_netpreds := map pair_to_nil netpreds;
       ts_tracepreds := map pair_to_nil tracepreds;
       ts_error := None |}.

  Definition random_test (netpreds : list netpred) (tracepreds : list tracepred) (init : net) (next : net -> nat -> operation) (n : nat) : test_state :=
    random_test_body (make_initial_state init netpreds tracepreds) next n.
End Shed.

Extraction "extraction/lib/ExtractedShed.ml" random_test np_const_true tp_const_true netpred.
