Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import StructTact.Update2.
Require Import StructTact.RemoveAll.
Require Import Sumbool.
Require Import Relation_Definitions.
Require Import RelationClasses.

Require Export Verdi.VerdiHints.

Require Import Cheerios.Cheerios.

Set Implicit Arguments.

Class BaseParams :=
  {
    data : Type;
    input : Type;
    output : Type
  }.

Class OneNodeParams (P : BaseParams) :=
  {
    init : data;
    handler : input -> data -> (output * data)
  }.

Class SingleParams (P : BaseParams) :=
  {
    init_handler : data;
    input_handler : input -> data -> (list output * data)
  }.

Class MultiParams (P : BaseParams) :=
  {
    name : Type ;
    msg : Type ;
    msg_eq_dec : forall x y : msg, {x = y} + {x <> y} ;
    name_eq_dec : forall x y : name, {x = y} + {x <> y} ;
    nodes : list name ;
    all_names_nodes : forall n, In n nodes ;
    no_dup_nodes : NoDup nodes ;
    init_handlers : name -> data;
    net_handlers : name -> name -> msg -> data -> (list output) * data * list (name * msg) ;
    input_handlers : name -> input -> data -> (list output) * data * list (name * msg)
  }.

Class FailureParams `(P : MultiParams) :=
  {
    reboot : data -> data
  }.

Definition do_disk file_name :=
  file_name -> option IOStreamWriter.t.

Inductive disk_op file_name :=
| Append :  file_name -> IOStreamWriter.t -> disk_op file_name
| Write : file_name -> IOStreamWriter.t -> disk_op file_name
| Delete : file_name -> disk_op file_name.

Class DiskOpMultiParams (P : BaseParams) :=
  {
    do_name : Type ;
    file_name : Type ;
    do_msg : Type ;
    do_msg_eq_dec : forall x y : do_msg, {x = y} + {x <> y} ;
    do_name_eq_dec : forall x y : do_name, {x = y} + {x <> y} ;
    file_name_eq_dec : forall x y : file_name, {x = y} + {x <> y} ;
    do_nodes : list do_name ;
    do_all_names_nodes : forall n, In n do_nodes ;
    do_no_dup_nodes : NoDup do_nodes ;
    do_net_handlers : do_name -> do_name -> do_msg -> data ->
                      list (disk_op file_name) * (list output) * data * list (do_name * do_msg) ;
    do_input_handlers : do_name -> input -> data ->
                        list (disk_op file_name) * (list output) * data * list (do_name * do_msg);
  }.

Class DiskOpFailureParams `(P : DiskOpMultiParams) :=
  {
    do_reboot : do_name -> (file_name -> option IOStreamWriter.in_channel) ->
                data * list (disk_op file_name)
  }.

Class NameOverlayParams `(P : MultiParams) :=
  {
    adjacent_to : relation name ;
    adjacent_to_dec : forall x y : name, {adjacent_to x y} + {~ adjacent_to x y} ;
    adjacent_to_symmetric : Symmetric adjacent_to ;
    adjacent_to_irreflexive : Irreflexive adjacent_to
  }.

Class FailMsgParams `(P : MultiParams) :=
  {
    msg_fail : msg
  }.

Class NewMsgParams `(P : MultiParams) :=
  {
    msg_new : msg
  }.

Section StepRelations.
  Variable A : Type.
  Variable trace : Type.

  Definition step_relation := A -> A -> list trace -> Prop.

  Inductive refl_trans_1n_trace (step : step_relation) : step_relation :=
  | RT1nTBase : forall x, refl_trans_1n_trace step x x []
  | RT1nTStep : forall x x' x'' cs cs',
                   step x x' cs ->
                   refl_trans_1n_trace step x' x'' cs' ->
                   refl_trans_1n_trace step x x'' (cs ++ cs').

  Theorem refl_trans_1n_trace_trans : forall step (a b c : A) (os os' : list trace),
                                        refl_trans_1n_trace step a b os ->
                                        refl_trans_1n_trace step b c os' ->
                                        refl_trans_1n_trace step a c (os ++ os').
  Proof using.
    intros.
    induction H; simpl; auto.
    concludes.
    rewrite app_ass.
    constructor 2 with x'; auto.
  Qed.

  Definition inductive (step : step_relation) (P : A -> Prop)  :=
    forall (a a': A) (os : list trace),
      P a ->
      step a a' os ->
      P a'.

  Theorem step_star_inductive :
    forall step P,
      inductive step P ->
      forall (a : A) a' os,
        P a ->
        (refl_trans_1n_trace step) a a' os ->
        P a'.
  Proof using.
    unfold inductive. intros.
    induction H1; auto.
    forwards; eauto.
  Qed.

  Definition inductive_invariant (step : step_relation) (init : A) (P : A -> Prop) :=
    P init /\ inductive step P.

  Definition reachable step init a :=
    exists out, refl_trans_1n_trace step init a out.

  Definition true_in_reachable step init (P : A -> Prop) :=
    forall a,
      reachable step init a ->
      P a.

  Theorem true_in_reachable_reqs :
    forall (step : step_relation) init (P : A -> Prop),
      (P init) ->
      (forall a a' out,
         step a a' out ->
         reachable step init a ->
         P a ->
         P a') ->
      true_in_reachable step init P.
  Proof using.
    intros. unfold true_in_reachable, reachable in *.
    intros. break_exists.
    match goal with H : refl_trans_1n_trace _ _ _ _ |- _ => induction H end;
      intuition eauto.
    match goal with H : P _ -> _ |- _ => apply H end;
      intros; break_exists;
      match goal with H : forall _ _ _, step _ _ _ -> _ |- _ => eapply H end;
      eauto; eexists; econstructor; eauto.
  Qed.

  Theorem inductive_invariant_true_in_reachable :
    forall step init P,
      inductive_invariant step init P ->
      true_in_reachable step init P.
  Proof using.
    unfold inductive_invariant, true_in_reachable, reachable, inductive in *. intros.
    break_exists.
    match goal with H : refl_trans_1n_trace _ _ _ _ |- _ => induction H end;
      intuition eauto.
  Qed.

  Inductive refl_trans_n1_trace (step : step_relation) : step_relation :=
  | RTn1TBase : forall x, refl_trans_n1_trace step x x []
  | RTn1TStep : forall x x' x'' cs cs',
                  refl_trans_n1_trace step x x' cs ->
                  step x' x'' cs' ->
                  refl_trans_n1_trace step x x'' (cs ++ cs').

  Lemma RTn1_step :
    forall (step : step_relation) x y z l l',
      step x y l ->
      refl_trans_n1_trace step y z l' ->
      refl_trans_n1_trace step x z (l ++ l').
  Proof using.
    intros.
    induction H0.
    - rewrite app_nil_r. rewrite <- app_nil_l.
      econstructor.
      constructor.
      auto.
    - concludes.
      rewrite <- app_ass.
      econstructor; eauto.
  Qed.

  Lemma refl_trans_1n_n1_trace :
    forall step x y l,
      refl_trans_1n_trace step x y l ->
      refl_trans_n1_trace step x y l.
  Proof using.
    intros.
    induction H.
    - constructor.
    - eapply RTn1_step; eauto.
  Qed.

  Lemma RT1n_step :
    forall (step : step_relation) x y z l l',
      refl_trans_1n_trace step x y l ->
      step y z l' ->
      refl_trans_1n_trace step x z (l ++ l').
  Proof using.
    intros.
    induction H.
    - simpl. rewrite <- app_nil_r. econstructor; eauto. constructor.
    - concludes. rewrite app_ass.
      econstructor; eauto.
  Qed.

  Lemma refl_trans_n1_1n_trace :
    forall step x y l,
      refl_trans_n1_trace step x y l ->
      refl_trans_1n_trace step x y l.
  Proof using.
    intros.
    induction H.
    - constructor.
    - eapply RT1n_step; eauto.
  Qed.

  Lemma refl_trans_1n_trace_n1_ind :
    forall (step : step_relation) (P : A -> A -> list trace -> Prop),
      (forall x, P x x []) ->
      (forall x x' x'' tr1 tr2,
         refl_trans_1n_trace step x x' tr1 ->
         step x' x'' tr2 ->
         P x x' tr1 ->
         refl_trans_1n_trace step x x'' (tr1 ++ tr2) ->
         P x x'' (tr1 ++ tr2)) ->
      forall x y l,
        refl_trans_1n_trace step x y l -> P x y l.
  Proof using.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    eapply refl_trans_n1_trace_ind; eauto.
    intros. eapply H0; eauto using refl_trans_n1_1n_trace, RT1n_step.
  Qed.

  Theorem true_in_reachable_elim :
    forall (step : step_relation) init (P : A -> Prop),
      true_in_reachable step init P ->
      (P init) /\
      (forall a a' out,
         step a a' out ->
         reachable step init a ->
         P a ->
         P a').
  Proof using.
    intros. unfold true_in_reachable, reachable in *.
    intros. intuition.
    - apply H; eexists; econstructor.
    - apply H.
      break_exists.
      eexists. apply refl_trans_n1_1n_trace.
      find_apply_lem_hyp refl_trans_1n_n1_trace.
      econstructor; eauto.
  Qed.
End StepRelations.

Section Step1.
  Context `{params : OneNodeParams}.

  Inductive step_1 : (step_relation data (input * output)) :=
  | S1T_deliver : forall (i : input) s s' (out : output),
                    handler i s = (out, s') ->
                    step_1 s s' [(i, out)].

  Definition step_1_star := refl_trans_1n_trace step_1.
End Step1.

Section StepSingle.
  Context `{params : SingleParams}.

  Inductive step_s : (step_relation data (input + output)) :=
  | SST_deliver : forall i s s' out tr,
                    input_handler i s = (out, s') ->
                    tr = inl i :: map inr out ->
                    step_s s s' tr.

  Definition step_s_star := refl_trans_1n_trace step_s.
End StepSingle.

Section StepAsync.

  Context `{params : MultiParams}.

  Record packet := mkPacket { pSrc  : name ;
                             pDst  : name ;
                             pBody : msg }.

  Definition send_packets src ps := (map (fun m => mkPacket src (fst m) (snd m)) ps).

  Definition packet_eq_dec (p q : packet) : {p = q} + {p <> q}.
    decide equality; auto using name_eq_dec, msg_eq_dec.
  Defined.

  Record network := mkNetwork { nwPackets : list packet ;
                               nwState   : name -> data }.

  Definition step_async_init : network :=
    mkNetwork [] init_handlers.

  Inductive step_async : step_relation network (name * (input + list output)) :=
  | StepAsync_deliver : forall net net' p xs ys out d l,
      nwPackets net = xs ++ p :: ys ->
      net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
      net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                       (update name_eq_dec (nwState net) (pDst p) d) ->
      step_async net net' [(pDst p, inr out)]
  (* inject a message (f inp) into host h. analogous to step_1 *delivery* *)
  | StepAsync_input : forall h net net' out inp d l,
      input_handlers h inp (nwState net h) = (out, d, l) ->
      net' = mkNetwork (send_packets h l ++ nwPackets net)
                       (update name_eq_dec (nwState net) h d) ->
      step_async net net' [(h, inl inp); (h, inr out)].

  Definition step_async_star := refl_trans_1n_trace step_async.
End StepAsync.

Arguments update _ _ _ _ _ _ / _.
Arguments send_packets _ _ _ _ /.

Section ParamsAux.
  Context `{params : MultiParams}.

  Lemma packet_eta :
    forall p : packet,
      {| pSrc := pSrc p; pDst := pDst p; pBody := pBody p |} = p.
  Proof using.
    destruct p; auto.
  Qed.

  Definition trace_non_empty_out (e : name * (input + list output)) :=
    match e with
    | (n, inr []) => None
    | _ => Some e
    end.
End ParamsAux.

Ltac map_id :=
  rewrite map_ext with (g := (fun x => x)); [eauto using map_id|simpl; intros; apply packet_eta].

Section StepDup.

  Context `{params : MultiParams}.

  Inductive step_dup : step_relation network (name * (input + list output)) :=
  (* just like step_async *)
  | StepDup_deliver : forall net net' p xs ys out d l,
      nwPackets net = xs ++ p :: ys ->
      net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
      net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                       (update name_eq_dec (nwState net) (pDst p) d) ->
      step_dup net net' [(pDst p, inr out)]
  (* inject a message (f inp) into host h *)
  | StepDup_input : forall h net net' out inp d l,
      input_handlers h inp (nwState net h) = (out, d, l) ->
      net' = mkNetwork (send_packets h l ++ nwPackets net)
                       (update name_eq_dec (nwState net) h d) ->
      step_dup net net' [(h, inl inp); (h, inr out)]
  | StepDup_dup : forall net net' p xs ys,
      nwPackets net = xs ++ p :: ys ->
      net' = mkNetwork (p :: xs ++ p :: ys) (nwState net) ->
      step_dup net net' [].

  Definition step_dup_star := refl_trans_1n_trace step_dup.
End StepDup.

Section StepDrop.

  Context `{params : MultiParams}.

  Inductive step_drop : step_relation network (name * (input + list output)) :=
  | StepDrop_deliver : forall net net' p xs ys out d l,
      nwPackets net = xs ++ p :: ys ->
      net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
      net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                       (update name_eq_dec (nwState net) (pDst p) d) ->
      step_drop net net' [(pDst p, inr out)]
  | StepDrop_drop : forall net net' p xs ys,
      nwPackets net = xs ++ p :: ys ->
      net' = mkNetwork (xs ++ ys) (nwState net) ->
      step_drop net net' []
  | StepDrop_input : forall h net net' out inp d l,
      input_handlers h inp (nwState net h) = (out, d, l) ->
      net' = mkNetwork (send_packets h l ++ nwPackets net)
                       (update name_eq_dec (nwState net) h d) ->
      step_drop net net' [(h, inl inp); (h, inr out)].

  Definition step_drop_star := refl_trans_1n_trace step_drop.
End StepDrop.

Section StepFailure.
  Context `{params : FailureParams}.

  (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_failure : step_relation (list name * network) (name * (input + list output)) :=
  (* like step_async, but only delivers to hosts that haven't failed yet *)
  | StepFailure_deliver : forall net net' failed p xs ys out d l,
      nwPackets net = xs ++ p :: ys ->
      ~ In (pDst p) failed ->
      net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
      net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                       (update name_eq_dec (nwState net) (pDst p) d) ->
      step_failure (failed, net) (failed, net') [(pDst p, inr out)]
  | StepFailure_input : forall h net net' failed out inp d l,
      ~ In h failed ->
      input_handlers h inp (nwState net h) = (out, d, l) ->
      net' = mkNetwork (send_packets h l ++ nwPackets net)
                       (update name_eq_dec (nwState net) h d) ->
      step_failure (failed, net) (failed, net') [(h, inl inp) ;  (h, inr out)]
  (* drops a packet *)
  | StepFailure_drop : forall net net' failed p xs ys,
      nwPackets net = xs ++ p :: ys ->
      net' = (mkNetwork (xs ++ ys) (nwState net)) ->
      step_failure (failed, net) (failed, net') []
  (* duplicates a packet *)
  | StepFailure_dup : forall net net' failed p xs ys,
      nwPackets net = xs ++ p :: ys ->
      net' = (mkNetwork (p :: xs ++ p :: ys) (nwState net)) ->
      step_failure (failed, net) (failed, net') []
  (* a host fails (potentially again) *)
  | StepFailure_fail :  forall h net failed,
      step_failure (failed, net) (h :: failed, net) []
  (* a host reboots (is not failing anymore). the new state is computed with the reboot function from the old state *)
  | StepFailure_reboot : forall h net net' failed failed',
      In h failed ->
      failed' = remove name_eq_dec h failed ->
      net' = mkNetwork (nwPackets net)
                       (update name_eq_dec (nwState net) h (reboot (nwState net h))) ->
      step_failure (failed, net) (failed', net') [].

  Definition step_failure_star : step_relation (list name * network) (name * (input + list output)) :=
    refl_trans_1n_trace step_failure.

  Definition step_failure_init : list name * network := ([], step_async_init).
End StepFailure.

Section StepFailureDiskOp.
  Context `{disk_op_failure_params : DiskOpFailureParams}.

  Record do_packet := mklPacket { do_pSrc  : do_name ;
                                 do_pDst  : do_name ;
                                 do_pBody : do_msg }.

  Definition do_send_packets src ps := (map (fun m => mklPacket src (fst m) (snd m)) ps).

  Definition do_packet_eq_dec (p q : do_packet) : {p = q} + {p <> q}.
    decide equality; auto using do_name_eq_dec, do_msg_eq_dec.
  Defined.

  Record do_network := mkdoNetwork { nwdoPackets : list do_packet ;
                                     nwdoState   : do_name -> data ;
                                     nwdoDisk    : do_name -> do_disk file_name
                                   }.

  Definition disk_to_channel (dsk : do_disk file_name) :=
    fun file => (match dsk file with
                 | Some s => Some (IOStreamWriter.channel_send (IOStreamWriter.out_channel_wrap s))
                 | None => None
                 end).

  Definition update_disk (dsk : do_disk file_name) (op : disk_op file_name) :
    do_disk file_name :=
    match op with
    | Append file x =>
      update file_name_eq_dec dsk file (match dsk file with
                                        | Some s => Some (s +$+ x)
                                        | None => Some x
                                        end)
    | Write file x => update file_name_eq_dec dsk file (Some x)
    | Delete file =>  update file_name_eq_dec dsk file (Some IOStreamWriter.empty)
    end.

  Definition apply_ops dsk ops :=
    fold_left update_disk ops dsk.

  Inductive step_failure_disk_ops : step_relation (list do_name * do_network) (do_name * (input + list output)) :=
  | StepFailureDiskOp_deliver : forall net net' failed p xs ys ops out d l,
      nwdoPackets net = xs ++ p :: ys ->
      ~ In (do_pDst p) failed ->
      do_net_handlers (do_pDst p) (do_pSrc p) (do_pBody p) (nwdoState net (do_pDst p)) = (ops, out, d, l) ->
      net' = mkdoNetwork (do_send_packets (do_pDst p) l ++ xs ++ ys)
               (update do_name_eq_dec (nwdoState net) (do_pDst p) d)
               (update do_name_eq_dec (nwdoDisk net) (do_pDst p) (apply_ops (nwdoDisk net (do_pDst p)) ops)) ->
      step_failure_disk_ops (failed, net) (failed, net') [(do_pDst p, inr out)]
  | StepFailureDiskOp_input : forall h net net' failed ops out inp d l,
      ~ In h failed ->
      do_input_handlers h inp (nwdoState net h) = (ops, out, d, l) ->
      net' = mkdoNetwork (do_send_packets h l ++ nwdoPackets net)
               (update do_name_eq_dec (nwdoState net) h d)
               (update do_name_eq_dec (nwdoDisk net) h (apply_ops (nwdoDisk net h) ops)) ->
      step_failure_disk_ops (failed, net) (failed, net') [(h, inl inp) ;  (h, inr out)]
  | StepFailureDiskOp_drop : forall net net' failed p xs ys,
      nwdoPackets net = xs ++ p :: ys ->
      net' = (mkdoNetwork (xs ++ ys) (nwdoState net) (nwdoDisk net)) ->
      step_failure_disk_ops (failed, net) (failed, net') []
  | StepFailureDiskOp_dup : forall net net' failed p xs ys,
      nwdoPackets net = xs ++ p :: ys ->
      net' = (mkdoNetwork (p :: xs ++ p :: ys) (nwdoState net) (nwdoDisk net)) ->
      step_failure_disk_ops (failed, net) (failed, net') []
  | StepFailureDiskOp_fail :  forall h net failed,
      step_failure_disk_ops (failed, net) (h :: failed, net) []
  | StepFailureDiskOp_reboot : forall h net net' failed failed' d ops,
      In h failed ->
      failed' = remove do_name_eq_dec h failed ->
      do_reboot h (disk_to_channel (nwdoDisk net h)) = (d, ops) ->
      net' = mkdoNetwork (nwdoPackets net)
               (update do_name_eq_dec (nwdoState net) h d)
               (update do_name_eq_dec (nwdoDisk net) h (apply_ops (nwdoDisk net h) ops)) ->
      step_failure_disk_ops (failed, net) (failed', net') [].

  Definition step_failure_disk_ops_star : step_relation (list do_name * do_network) (do_name * (input + list output)) :=
    refl_trans_1n_trace step_failure_disk_ops.

  Definition null_disk : do_disk file_name :=
    fun _ => None.

  Definition step_failure_disk_ops_init : list do_name * do_network :=
    ([], mkdoNetwork [] (fun h => fst (do_reboot h (disk_to_channel null_disk)))
      (fun h => apply_ops null_disk (snd (do_reboot h (disk_to_channel null_disk))))).
End StepFailureDiskOp.

Section StepOrdered.
  Context `{params : MultiParams}.

  Notation src := name (only parsing).
  Notation dst := name (only parsing).

  Record ordered_network :=
    mkONetwork
       { onwPackets : src -> dst -> list msg;
         onwState   : name -> data
       }.

  Inductive step_ordered : step_relation ordered_network (name * (input + output)) :=
  | StepOrdered_deliver : forall net net' tr m ms out d l from to,
      onwPackets net from to = m :: ms ->
      net_handlers to from m (onwState net to) = (out, d, l) ->
      net' = mkONetwork (collate name_eq_dec to (update2 name_eq_dec (onwPackets net) from to ms) l)
                        (update name_eq_dec (onwState net) to d) ->
      tr = map2fst to (map inr out) ->
      step_ordered net net' tr
  | StepOrdered_input : forall h net net' tr out inp d l,
      input_handlers h inp (onwState net h) = (out, d, l) ->
      net' = mkONetwork (collate name_eq_dec h (onwPackets net) l)
                        (update name_eq_dec (onwState net) h d) ->
      tr = (h, inl inp) :: map2fst h (map inr out) ->
      step_ordered net net' tr.

  Definition step_ordered_star := refl_trans_1n_trace step_ordered.

  Definition step_ordered_init : ordered_network := mkONetwork (fun _ _ => []) init_handlers.
End StepOrdered.

Section StepOrderedFailure.
  Context `{multi_params : MultiParams}.
  Context {overlay_params : NameOverlayParams multi_params}.
  Context {fail_msg_params : FailMsgParams multi_params}.

  Inductive step_ordered_failure : step_relation (list name * ordered_network) (name * (input + output)) :=
  | StepOrderedFailure_deliver : forall net net' failed tr m ms out d l from to,
      onwPackets net from to = m :: ms ->
      ~ In to failed ->
      net_handlers to from m (onwState net to) = (out, d, l) ->
      net' = {| onwPackets := collate name_eq_dec to (update2 name_eq_dec (onwPackets net) from to ms) l;
                onwState := update name_eq_dec (onwState net) to d |} ->
      tr = map2fst to (map inr out) ->
      step_ordered_failure (failed, net) (failed, net') tr
  | StepOrderedFailure_input : forall h net net' failed tr out inp d l,
      ~ In h failed ->
      input_handlers h inp (onwState net h) = (out, d, l) ->
      net' = {| onwPackets := collate name_eq_dec h (onwPackets net) l;
                onwState := update name_eq_dec (onwState net) h d |} ->
      tr = (h, inl inp) :: map2fst h (map inr out) ->
      step_ordered_failure (failed, net) (failed, net') tr
  | StepOrderedFailure_fail :  forall h net net' failed,
      ~ In h failed ->
      net' = {| onwPackets := collate name_eq_dec h (onwPackets net)
                  (map2snd msg_fail (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed nodes))) ;
                onwState := onwState net |} ->
      step_ordered_failure (failed, net) (h :: failed, net') [].

  Definition step_ordered_failure_star := refl_trans_1n_trace step_ordered_failure.

  Definition step_ordered_failure_init : list name * ordered_network := ([], step_ordered_init).
End StepOrderedFailure.

Section StepOrderedDynamic.
  Context `{multi_params : MultiParams}.
  Context {overlay_params : NameOverlayParams multi_params}.
  Context {new_msg_params : NewMsgParams multi_params}.

  Notation src := name (only parsing).
  Notation dst := name (only parsing).

  Record ordered_dynamic_network :=
    mkODNetwork
       {
         odnwNodes : list name ;
         odnwPackets : src -> dst -> list msg ;
         odnwState : name -> option data
       }.

  Inductive step_ordered_dynamic : step_relation ordered_dynamic_network (name * (input + output)) :=
  | StepOrderedDynamic_start : forall net net' h,
      ~ In h (odnwNodes net) ->
      net' = {| odnwNodes := h :: odnwNodes net;
                odnwPackets := collate_ls name_eq_dec (filter_rel adjacent_to_dec h (odnwNodes net))
                               (collate name_eq_dec h (odnwPackets net)
                                 (map2snd msg_new (filter_rel adjacent_to_dec h (odnwNodes net)))) h msg_new;
                odnwState := update name_eq_dec (odnwState net) h (Some (init_handlers h)) |} ->
      step_ordered_dynamic net net' []
  | StepOrderedDynamic_deliver : forall net net' tr m ms out d d' l from to,
      In to (odnwNodes net) ->
      odnwState net to = Some d ->
      odnwPackets net from to = m :: ms ->
      net_handlers to from m d = (out, d', l) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate name_eq_dec to (update2 name_eq_dec (odnwPackets net) from to ms) l;
                odnwState := update name_eq_dec (odnwState net) to (Some d') |} ->
      tr = map2fst to (map inr out) ->
      step_ordered_dynamic net net' tr
  | StepOrderedDynamic_input : forall h net net' tr out inp d d' l,
      In h (odnwNodes net) ->
      odnwState net h = Some d ->
      input_handlers h inp d = (out, d', l) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate name_eq_dec h (odnwPackets net) l;
                odnwState := update name_eq_dec (odnwState net) h (Some d') |} ->
      tr = (h, inl inp) :: map2fst h (map inr out) ->
      step_ordered_dynamic net net' tr.

  Definition step_ordered_dynamic_star := refl_trans_1n_trace step_ordered_dynamic.

  Definition step_ordered_dynamic_init : ordered_dynamic_network := mkODNetwork [] (fun _ _ => []) (fun _ => None).
End StepOrderedDynamic.

Section StepOrderedDynamicFailure.
  Context `{multi_params : MultiParams}.
  Context {overlay_params : NameOverlayParams multi_params}.
  Context {new_msg_params : NewMsgParams multi_params}.
  Context {fail_msg_params : FailMsgParams multi_params}.

  Inductive step_ordered_dynamic_failure : step_relation (list name * ordered_dynamic_network) (name * (input + output)) :=
  | StepOrderedDynamicFailure_start : forall net net' failed h,
      ~ In h (odnwNodes net) ->
      net' = {| odnwNodes := h :: odnwNodes net;
                odnwPackets := collate_ls name_eq_dec (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed (odnwNodes net)))
                                (collate name_eq_dec h (odnwPackets net)
                                  (map2snd msg_new (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed (odnwNodes net))))) h msg_new;
                odnwState := update name_eq_dec (odnwState net) h (Some (init_handlers h)) |} ->
      step_ordered_dynamic_failure (failed, net) (failed, net') []
  | StepOrderedDynamicFailure_deliver : forall net net' failed tr m ms out d d' l from to,
      ~ In to failed ->
      In to (odnwNodes net) ->
      odnwState net to = Some d ->
      odnwPackets net from to = m :: ms ->
      net_handlers to from m d = (out, d', l) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate name_eq_dec to (update2 name_eq_dec (odnwPackets net) from to ms) l;
                odnwState := update name_eq_dec (odnwState net) to (Some d') |} ->
      tr = map2fst to (map inr out) ->
      step_ordered_dynamic_failure (failed, net) (failed, net') tr
  | StepOrderedDynamicFailure_input : forall h net net' failed tr out inp d d' l,
      ~ In h failed ->
      In h (odnwNodes net) ->
      odnwState net h = Some d ->
      input_handlers h inp d = (out, d', l) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate name_eq_dec h (odnwPackets net) l;
                odnwState := update name_eq_dec (odnwState net) h (Some d') |} ->
      tr = (h, inl inp) :: map2fst h (map inr out) ->
      step_ordered_dynamic_failure (failed, net) (failed, net') tr
  | StepOrderedDynamicFailure_fail : forall h net net' failed,
      ~ In h failed ->
      In h (odnwNodes net) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate name_eq_dec h (odnwPackets net)
                                (map2snd msg_fail (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed (odnwNodes net)))) ;
                odnwState := odnwState net |} ->
      step_ordered_dynamic_failure (failed, net) (h :: failed, net') [].

  Definition step_ordered_dynamic_failure_star := refl_trans_1n_trace step_ordered_dynamic_failure.

  Definition step_ordered_dynamic_failure_init : list name * ordered_dynamic_network :=
    ([], step_ordered_dynamic_init).
End StepOrderedDynamicFailure.
