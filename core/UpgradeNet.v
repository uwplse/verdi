Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Require Import VerdiTactics.

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

Class VerySimpleUpdateParams :=
  {
    name : Type ;
    msg : Type ;
    input : Type ;
    output : Type ;
    
    msg_eq_dec : forall x y : msg, {x = y} + {x <> y} ;
    name_eq_dec : forall x y : name, {x = y} + {x <> y} ;
    
    nodes : list name ;
    all_names_nodes : forall n, In n nodes ;
    no_dup_nodes : NoDup nodes ;

    data1 : Type;
    init_handlers : name -> data1 ;
    net_handlers1 : name -> name -> msg -> data1 -> (list output) * data1 * list (name * msg) ;
    input_handlers1 : name -> input -> data1 -> (list output) * data1 * list (name * msg) ;
    reboot1 : data1 -> data1 ;
    
    data2 : Type;
    net_handlers2 : name -> name -> msg -> data2 -> (list output) * data2 * list (name * msg) ;
    input_handlers2 : name -> input -> data2 -> (list output) * data2 * list (name * msg) ;
    reboot2 : data2 -> data2 ;

    upgrade : data1 -> data2
  }.


Section StepVerySimpleUpdate.
  Context `{params : VerySimpleUpdateParams}.

  Inductive version :=
  | One
  | Two.

  Definition data (v : version) : Type :=
    match v with
    | One => data1
    | Two => data2
    end.

  Definition state := sigT data.

  Definition upgrade_state (sigma : state) : state :=
    let (v, d) := sigma in
    match v as v' return (data v' -> state) with
    | One => fun d => existT _ Two (upgrade d)
    | Two => fun d => existT _ Two d
    end d.

  Definition net_handlers  (me : name) (src : name) (m : msg) (sigma : state) :
    list output * state * list (name * msg) :=
    let (v, d) := sigma in
    match v as v' return (data v' -> (list output * state * list (name * msg))) with
    | One =>
      fun d =>
        let '(os, d', ms) := net_handlers1 me src m d in
        (os, existT _ One d', ms)
    | Two =>
      fun d =>
        let '(os, d', ms) := net_handlers2 me src m d in
        (os, existT _ Two d', ms)
    end d.

  Definition input_handlers  (me : name) (inp : input) (sigma : state) :
    list output * state * list (name * msg) :=
    let (v, d) := sigma in
    match v as v' return (data v' -> (list output * state * list (name * msg))) with
    | One =>
      fun d =>
        let '(os, d', ms) := input_handlers1 me inp d in
        (os, existT _ One d', ms)
    | Two =>
      fun d =>
        let '(os, d', ms) := input_handlers2 me inp d in
        (os, existT _ Two d', ms)
    end d.
  
  Definition reboot (sigma: state) : state :=
    let (v, d) := sigma in
    match v as v' return (data v' -> state) with
    | One =>
      fun d =>
        existT _ One (reboot1 d)
    | Two =>
      fun d =>
        existT _ Two (reboot2 d)
    end d.

  Record packet := mkPacket { pSrc  : name;
                              pDst  : name;
                              pBody : msg }.
  
  Record network :=
    mkNetwork
      {
        nwFailed : list name ;
        nwPackets : list packet ;
        nwState : name -> state
      }.

  Definition update {A : Type} st h (v : A) := (fun nm => if name_eq_dec nm h then v else st nm).
  Definition send_packets src ps := (map (fun m => mkPacket src (fst m) (snd m)) ps).


    (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_u : step_relation network (name * (input + list output)) :=
  (* like step_m, but only delivers to hosts that haven't failed yet *)
  | SU_deliver : forall net net' p xs ys out d l,
                nwPackets net = xs ++ p :: ys ->
                ~ In (pDst p) (nwFailed net) ->
                net_handlers (pDst p) (pSrc p) (pBody p)
                             (nwState net (pDst p)) = (out, d, l) ->
                net' = mkNetwork
                         (nwFailed net)
                         (send_packets (pDst p) l ++ xs ++ ys)
                         (update (nwState net) (pDst p) d) ->
                step_u net net' [(pDst p, inr out)]
  | SU_input : forall h net net' out inp d l,
                 ~ In h (nwFailed net) ->
                 input_handlers h inp (nwState net h) = (out, d, l) ->
                 net' = mkNetwork
                          (nwFailed net)
                          (send_packets h l ++ nwPackets net)
                          (update (nwState net) h d) ->
                 step_u net net' [(h, inl inp) ;  (h, inr out)]
  (* drops a packet *)
  | SU_drop : forall net net' p xs ys,
                nwPackets net = xs ++ p :: ys ->
                net' = mkNetwork
                         (nwFailed net)
                         (xs ++ ys)
                         (nwState net) ->
                step_u net net' []
  (* duplicates a packet *)
  | SU_dup : forall net net' p xs ys,
                nwPackets net = xs ++ p :: ys ->
                net' = mkNetwork
                         (nwFailed net)
                         (p :: xs ++ p ::ys)
                         (nwState net) ->
                step_u net net' []
  (* a host fails (potentially again) *)
  | SU_fail :  forall h net net',
                 net' = mkNetwork
                          (h :: nwFailed net)
                          (nwPackets net)
                          (nwState net) ->
                 step_u net net' []
  (* a host reboots (is not failing anymore). the new state is computed with the reboot function from the old state *)
  | SU_reboot : forall h net net' d,
                  In h (nwFailed net) ->
                  reboot (nwState net h) = d ->
                  net' = mkNetwork
                           (remove name_eq_dec h (nwFailed net))
                           (nwPackets net)
                           (update (nwState net) h d) ->
                  step_u net net' []
  | SU_update : forall h net net' d,
                  ~ In h (nwFailed net) ->
                  upgrade_state (nwState net h) = d ->
                  net' = mkNetwork
                           (nwFailed net)
                           (nwPackets net)
                           (update (nwState net) h d) ->
                  step_u net net' [].

  Definition step_u_star := refl_trans_1n_trace _ _ step_u.
  Definition step_u_init : network :=
    mkNetwork
      []
      []
      (fun n =>
         existT _ One (init_handlers n)).
End StepVerySimpleUpdate.

