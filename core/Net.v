Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Export VerdiHints.

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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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

Section StepAsync.

  Context `{params : MultiParams}.

  Definition update {A : Type} st h (v : A) := (fun nm => if name_eq_dec nm h then v else st nm).

  Record packet := mkPacket { pSrc  : name;
                              pDst  : name;
                              pBody : msg }.

  Definition send_packets src ps := (map (fun m => mkPacket src (fst m) (snd m)) ps).

  Definition packet_eq_dec (p q : packet) : {p = q} + {p <> q}.
    decide equality; auto using name_eq_dec, msg_eq_dec.
  Defined.

  Record network := mkNetwork { nwPackets : list packet;
                                nwState   : name -> data }.

  Definition step_m_init : network :=
    mkNetwork [] init_handlers.

  Inductive step_m : step_relation network (name * (input + list output)) :=
  | SM_deliver : forall net net' p xs ys out d l,
                     nwPackets net = xs ++ p :: ys ->
                     net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                     net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                      (update (nwState net) (pDst p) d) ->
                     step_m net net' [(pDst p, inr out)]
  (* inject a message (f inp) into host h. analogous to step_1 *delivery* *)
  | SM_input : forall h net net' out inp d l,
                   input_handlers h inp (nwState net h) = (out, d, l) ->
                   net' = mkNetwork (send_packets h l ++ nwPackets net)
                                    (update (nwState net) h d) ->
                   step_m net net' [(h, inl inp); (h, inr out)].

  Definition step_m_star := refl_trans_1n_trace step_m.
End StepAsync.

Arguments update _ _ _ _ _ _ / _.
Arguments send_packets _ _ _ _ /.

Section packet_eta.
  Context {P : BaseParams}.
  Context {M : @MultiParams P}.

  Lemma packet_eta :
    forall p : @packet P M,
      {| pSrc := pSrc p; pDst := pDst p; pBody := pBody p |} = p.
  Proof.
    destruct p; auto.
  Qed.
End packet_eta.

Ltac map_id :=
  rewrite map_ext with (g := (fun x => x)); [eauto using map_id|simpl; intros; apply packet_eta].

Section StepDup.
  
  Context `{params : MultiParams}.

  Inductive step_d : step_relation network (name * (input + list output)) :=
  (* just like step_m *)
  | SD_deliver : forall net net' p xs ys out d l,
                     nwPackets net = xs ++ p :: ys ->
                     net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                     net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                      (update (nwState net) (pDst p) d) ->
                     step_d net net' [(pDst p, inr out)]
  (* inject a message (f inp) into host h *)
  | SD_input : forall h net net' out inp d l,
                   input_handlers h inp (nwState net h) = (out, d, l) ->
                   net' = mkNetwork (send_packets h l ++ nwPackets net)
                                    (update (nwState net) h d) ->
                   step_d net net' [(h, inl inp); (h, inr out)]
  | SD_dup : forall net net' p xs ys,
               nwPackets net = xs ++ p :: ys ->
               net' = mkNetwork (p :: xs ++ p :: ys)
                                (nwState net) ->
               step_d net net' [].

  Definition step_d_star := refl_trans_1n_trace step_d.
End StepDup.

Section StepDrop.

  Context `{params : MultiParams}.

  Inductive step_drop : step_relation network (name * (input + list output)) :=
  | Sdrop_deliver : forall net net' p xs ys out d l,
                     nwPackets net = xs ++ p :: ys ->
                     net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                     net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                      (update (nwState net) (pDst p) d) ->
                     step_drop net net' [(pDst p, inr out)]
  | Sdrop_drop : forall net net' p xs ys,
                  nwPackets net = xs ++ p :: ys ->
                  net' = mkNetwork (xs ++ ys) (nwState net) ->
                  step_drop net net' []
  | Sdrop_input : forall h net net' out inp d l,
                   input_handlers h inp (nwState net h) = (out, d, l) ->
                   net' = mkNetwork (send_packets h l ++ nwPackets net)
                                    (update (nwState net) h d) ->
                   step_drop net net' [(h, inl inp); (h, inr out)].

  Definition step_drop_star := refl_trans_1n_trace step_drop.
End StepDrop.

Section StepFailure.
  Context `{params : FailureParams}.

    (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_f : step_relation (list name * network) (name * (input + list output)) :=
  (* like step_m, but only delivers to hosts that haven't failed yet *)
  | SF_deliver : forall net net' failed p xs ys out d l,
                nwPackets net = xs ++ p :: ys ->
                ~ In (pDst p) failed ->
                net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                 (update (nwState net) (pDst p) d) ->
                step_f (failed, net) (failed, net') [(pDst p, inr out)]
  | SF_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                  input_handlers h inp (nwState net h) = (out, d, l) ->
                  net' = mkNetwork (send_packets h l ++ nwPackets net)
                                   (update (nwState net) h d) ->
                  step_f (failed, net) (failed, net') [(h, inl inp) ;  (h, inr out)]
  (* drops a packet *)
  | SF_drop : forall net net' failed p xs ys,
                nwPackets net = xs ++ p :: ys ->
                net' = (mkNetwork (xs ++ ys) (nwState net)) ->
                step_f (failed, net) (failed, net') []
  (* duplicates a packet *)
  | SF_dup : forall net net' failed p xs ys,
               nwPackets net = xs ++ p :: ys ->
               net' = (mkNetwork (p :: xs ++ p :: ys) (nwState net)) ->
               step_f (failed, net) (failed, net') []
  (* a host fails (potentially again) *)
  | SF_fail :  forall h net failed,
                 step_f (failed, net) (h :: failed, net) []
  (* a host reboots (is not failing anymore). the new state is computed with the reboot function from the old state *)
  | SF_reboot : forall h net net' failed failed',
                  In h failed ->
                  failed' = remove name_eq_dec h failed ->
                  net' = mkNetwork (nwPackets net)
                                   (fun nm => if name_eq_dec nm h then
                                               (reboot (nwState net nm))
                                             else
                                               (nwState net nm)) ->
                  step_f (failed, net) (failed', net') [].

  Definition step_f_star : step_relation (list name * network) (name * (input + list output)) :=
    refl_trans_1n_trace step_f.

  Definition step_f_init : list name * network := ([], step_m_init).
End StepFailure.

Record handlerUpdate `(P : FailureParams) :=
  {
    huInput :  name -> input -> data -> (list output) * data * list (name * msg);
    huNet : name -> name -> msg -> data -> (list output) * data * list (name * msg);
    huReboot : data -> data;
    huUpdate : name -> data -> (list output) * data * list (name * msg)
  }.

Class SimpleUpdateParams `(P : FailureParams) :=
  {
    updates : list (handlerUpdate P)
  }.

Inductive Nth {A : Type} : list A -> nat -> A -> Prop :=
| Nth_0 : forall x l, Nth (x :: l) 0 x
| Nth_S : forall l x n y, Nth l n x -> Nth (y :: l) (S n) x.

Lemma nth_error_Nth :
  forall A n l (x : A),
    nth_error l n = Some x ->
    Nth l n x.
Proof.
  induction n; intros; simpl in *; auto.
  - break_match; try discriminate.
    unfold value in *.
    find_inversion.
    constructor.
  - break_match; try discriminate.
    subst. constructor.
    eauto.
Qed.

Lemma Nth_nth_error :
  forall A n l (x : A),
    Nth l n x ->
    nth_error l n = Some x.
Proof.
  intros.
  induction H; simpl in *; auto.
Qed.

Section StepSimpleUpdate.
  Context `{params : SimpleUpdateParams}.

    (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_u : step_relation ((name -> nat) * list name * network) (name * (input + list output)) :=
  (* like step_m, but only delivers to hosts that haven't failed yet *)
  | SU_deliver : forall up net net' handlers failed p xs ys out d l,
                nwPackets net = xs ++ p :: ys ->
                ~ In (pDst p) failed ->
                Nth updates (up (pDst p)) handlers ->
                (huNet handlers) (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                 (update (nwState net) (pDst p) d) ->
                step_u (up, failed, net) (up, failed, net') [(pDst p, inr out)]
  | SU_input : forall up h net net' handlers failed out inp d l,
                 ~ In h failed ->
                 Nth updates (up h) handlers ->
                 (huInput handlers) h inp (nwState net h) = (out, d, l) ->
                 net' = mkNetwork (send_packets h l ++ nwPackets net)
                                  (update (nwState net) h d) ->
                 step_u (up, failed, net) (up, failed, net') [(h, inl inp) ;  (h, inr out)]
  (* drops a packet *)
  | SU_drop : forall up net net' failed p xs ys,
                nwPackets net = xs ++ p :: ys ->
                net' = (mkNetwork (xs ++ ys) (nwState net)) ->
                step_u (up, failed, net) (up, failed, net') []
  (* duplicates a packet *)
  | SU_dup : forall up net net' failed p xs ys,
               nwPackets net = xs ++ p :: ys ->
               net' = (mkNetwork (p :: xs ++ p :: ys) (nwState net)) ->
               step_u (up, failed, net) (up, failed, net') []
  (* a host fails (potentially again) *)
  | SU_fail :  forall up h net failed,
                 step_u (up, failed, net) (up, h :: failed, net) []
  (* a host reboots (is not failing anymore). the new state is computed with the reboot function from the old state *)
  | SU_reboot : forall up h net net' handlers failed failed',
                  In h failed ->
                  failed' = remove name_eq_dec h failed ->
                  Nth updates (up h) handlers ->
                  net' = mkNetwork (nwPackets net)
                                   (fun nm => if name_eq_dec nm h then
                                               (huReboot handlers (nwState net nm))
                                             else
                                               (nwState net nm)) ->
                  step_u (up, failed, net) (up, failed', net') []
  | SU_update : forall up h net net' handlers failed out d l,
                  ~ In h failed ->
                  Nth updates (S (up h)) handlers ->
                  (huUpdate handlers) h (nwState net h) = (out, d, l) ->
                  net' = mkNetwork (send_packets h l ++ nwPackets net)
                                   (update (nwState net) h d) ->
                  step_u (up, failed, net) ((update up h (S (up h))), failed, net') [(h, inr out)].

  Definition step_u_star : step_relation ((name -> nat) *list name * network) (name * (input + list output)) :=
    refl_trans_1n_trace step_u.

  Definition step_u_init : (name -> nat) * list name * network := (fun _ => 0, [], step_m_init).
End StepSimpleUpdate.
