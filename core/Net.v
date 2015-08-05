Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import FunctionalExtensionality.
Require Import Relations.Relation_Operators.
Require Import Relations.Operators_Properties.
Require Import Util.
Require Import VerdiTactics.

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
  (* just like step_m *)
  | SM_deliver : forall net net' p xs ys out d l,
                     nwPackets net = xs ++ p :: ys ->
                     net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                     net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                      (update (nwState net) (pDst p) d) ->
                     step_m net net' [(pDst p, inr out)]
  (* inject a message (f inp) into host h *)
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

Class GhostFailureParams `(P : FailureParams) :=
  {
    ghost_data : Type;
    ghost_init : ghost_data ;
    ghost_net_handlers :
      name -> name -> msg -> (ghost_data * data) -> ghost_data;
    ghost_input_handlers :
      name -> input -> (ghost_data * data) -> ghost_data
  }.

Section GhostVars.
  Context {base_params : BaseParams}.
  Context {multi_params : MultiParams base_params}.
  Context {failure_params : FailureParams multi_params}.
  Context {params : GhostFailureParams failure_params}.

  Definition refined_net_handlers me src m st :=
    let '(out, st', ps) :=
        net_handlers me src m (snd st) in
    (out, (ghost_net_handlers me src m st, st'), ps).

  Definition refined_input_handlers me inp st :=
    let '(out, st', ps) :=
        input_handlers me inp (snd st) in
    (out, (ghost_input_handlers me inp st, st'), ps).

  Definition refined_reboot (st : ghost_data * data) :=
    (fst st , reboot (snd st)).

  Definition refined_init_handlers (n : name) : ghost_data * data :=
    (ghost_init, init_handlers n).

  Instance refined_base_params : BaseParams :=
    {
      data := (ghost_data * data)%type ;
      input := input ;
      output := output
    }.

  Instance refined_multi_params : MultiParams _ :=
    {
      name := name ;
      msg := msg ;
      msg_eq_dec := msg_eq_dec ;
      name_eq_dec := name_eq_dec ;
      nodes := nodes ;
      all_names_nodes := all_names_nodes ;
      no_dup_nodes := no_dup_nodes ;
      init_handlers := refined_init_handlers;
      net_handlers := refined_net_handlers ;
      input_handlers := refined_input_handlers
    }.

  Instance refined_failure_params : FailureParams _ :=
    {
      reboot := refined_reboot
    }.

  Definition deghost_packet p :=
    @mkPacket _ multi_params
              (@pSrc _ refined_multi_params p)
              (pDst p)
              (pBody p).

  Definition deghost (net : @network _ refined_multi_params) : (@network _ multi_params).
    refine (@mkNetwork _ multi_params

                       (map deghost_packet
                          (nwPackets net))
                       _
           ).
    intros.
    destruct net.
    concludes.
    destruct nwState0. auto.
  Defined.

  Arguments deghost_packet /_.


  Definition deghost_prop I (failed_net : list name * network) : Prop :=
    I ((fst failed_net), deghost (snd failed_net)).

  Require Import FunctionalExtensionality.

  Ltac workhorse :=
    try match goal with
        | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal
      end;
    try match goal with
        | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros
      end;
      repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => invc H
             end;
      repeat (simpl in *; subst);
      repeat rewrite map_app;
      repeat rewrite map_map.

  Theorem ghost_simulation_1 :
    forall net net' failed failed' out,
      @step_f _ _ refined_failure_params (failed, net) (failed', net') out ->
      @step_f _ _ failure_params (failed, deghost net) (failed', deghost net') out.
  Proof.
    intros.
    invcs H;
      unfold refined_net_handlers,
             refined_input_handlers,
             refined_reboot,
             deghost
               in *;
      workhorse;
    [(match goal with
          [ p : packet |- _ ] =>
            assert (pDst p = pDst (deghost_packet p)) by
              (destruct p; simpl in *; solve_by_inversion);
          repeat find_rewrite
      end);
      econstructor 1
      | econstructor 2
      | econstructor 3
      | econstructor 4
      | econstructor 5
      | econstructor 6
      ]; simpl; eauto;
      workhorse;
      congruence.
  Qed.

  Definition ghost_packet p :=
    @mkPacket _ refined_multi_params
              (@pSrc _ multi_params p)
              (pDst p)
              (pBody p).


  Definition reghost (net : @network _ multi_params) : @network _ refined_multi_params.
    refine (@mkNetwork _ refined_multi_params
                       (map ghost_packet
                          (nwPackets net))
                       _
           ).
    intros.
    destruct net.
    concludes.
    exact (ghost_init, nwState0).
  Defined.

  Arguments ghost_packet /_.

  Lemma reghost_deghost_partial_inverses :
    forall net,
      deghost (reghost net) = net.
  Proof.
    destruct net. unfold deghost, reghost. simpl in *. f_equal.
    rewrite map_map. map_id.
  Qed.

  Theorem ghost_simulation_2 :
    forall net net' failed failed' out gnet,
      @step_f _ _ failure_params (failed, net) (failed', net') out ->
      deghost gnet = net ->
      exists gnet',
        step_f (failed, gnet) (failed', gnet') out /\
        deghost gnet' = net'.
  Proof.
    intros.
    invcs H.
    - repeat break_match. simpl in *.
      match goal with
        | H : map _ ?la = ?lb |- _ =>
          symmetry in H;
            pose proof @map_inverses _ _ la lb deghost_packet ghost_packet
      end.
      repeat (forwards; [intro a; destruct a; reflexivity|]; concludes;
              match goal with
                | H :  forall _ : packet,  _ = _ |- _ => clear H
              end).
      concludes. map_crush.
      match goal with
        | [ _ : _ = ?xs ++ ?p :: ?ys,
              _ : net_handlers ?h ?s ?m ?d = (_, ?d', ?l),
                  _ : (?nwState ?h = (?g, ?d)) |- _ ] =>
          exists {| nwPackets := (map ghost_packet (send_packets h l) ++ xs ++ ys) ;
               nwState := update nwState h (ghost_net_handlers h s m (g, d), d') |}
      end.
      intuition.
      + simpl in *. map_crush.
        subst.
        match goal with
            [ p : packet |- _ ] =>
            assert (pDst p = pDst (ghost_packet p)) by
                (destruct p; simpl in *; solve_by_inversion);
              repeat find_rewrite
         end.
        eapply (@SF_deliver _ _ refined_failure_params); simpl in *; eauto.
        simpl in *.
        unfold refined_net_handlers. repeat break_match.
        subst.
        repeat (find_rewrite; simpl in *). find_inversion. eauto.
      + unfold deghost. simpl in *. map_crush. repeat f_equal; try map_id.
        apply functional_extensionality. intros.
        repeat break_match; congruence.
   - repeat break_match. subst. simpl in *.
      match goal with
        | [ pkts: list packet, _ : input_handlers ?h ?inp ?d = (_, ?d', ?l),
                                   _ : (?nwState ?h = (?g, ?d)) |- _ ] =>
          exists {| nwPackets := (map ghost_packet (send_packets h l)) ++ pkts ;
               nwState := update nwState h (ghost_input_handlers h inp (g, d), d') |}
      end.
      intuition.
      + simpl in *. map_crush.
        subst. eapply (@SF_input _ _ refined_failure_params); simpl in *; eauto.
        simpl in *.
        unfold refined_input_handlers. repeat break_match.
        subst.
        repeat (find_rewrite; simpl in *). find_inversion. auto.
      + unfold deghost. simpl in *. map_crush. repeat f_equal; try map_id.
        apply functional_extensionality. intros.
        repeat break_match; congruence.
   - match goal with
        | H : map _ ?la = ?lb |- _ =>
          symmetry in H;
            pose proof @map_inverses _ _ la lb deghost_packet ghost_packet
      end.
      repeat (forwards; [intro a; destruct a; reflexivity|]; concludes;
              match goal with
                | H :  forall _ : packet,  _ = _ |- _ => clear H
              end).
      concludes. map_crush.
      exists {| nwPackets := map ghost_packet (xs ++ ys) ;
          nwState := fun h => nwState gnet h |}.
     intuition.
     + eapply (@SF_drop _ _ refined_failure_params); simpl in *; eauto.
       map_crush. intuition.
     + unfold deghost. simpl in *. map_crush. repeat f_equal; try map_id.
       apply functional_extensionality. intros.
       repeat break_match. simpl in *. congruence.
   - match goal with
        | H : map _ ?la = ?lb |- _ =>
          symmetry in H;
            pose proof @map_inverses _ _ la lb deghost_packet ghost_packet
      end.
      repeat (forwards; [intro a; destruct a; reflexivity|]; concludes;
              match goal with
                | H :  forall _ : packet,  _ = _ |- _ => clear H
              end).
      concludes. map_crush.
      exists {| nwPackets := map ghost_packet (p :: xs ++ p :: ys) ;
          nwState := fun h => nwState gnet h |}.
     intuition.
     + eapply (@SF_dup _ _ refined_failure_params); simpl in *; eauto.
       map_crush. intuition.
     + unfold deghost. simpl in *. map_crush.
       repeat f_equal; try map_id; try match goal with
                                         | [ |- _ = ?p] => destruct p; reflexivity
                                       end.
       apply functional_extensionality. intros.
       repeat break_match. simpl in *. congruence.
   - exists gnet. intuition.
       apply (@SF_fail _ _ refined_failure_params).
   - exists {| nwPackets := nwPackets gnet;
          nwState := update (nwState gnet) h (refined_reboot (nwState gnet h))
       |}.
       intuition.
       + eapply (@SF_reboot _ _ refined_failure_params); eauto.
         f_equal. simpl in *. apply functional_extensionality.
         intros. break_if; congruence.
       + unfold deghost. simpl in *.  f_equal.
         apply functional_extensionality. intros.
         unfold refined_reboot.
         repeat break_match; simpl in *.
         * repeat find_inversion. repeat find_rewrite. reflexivity.
         * congruence.
  Qed.

  Theorem ghost_invariant_lift :
    forall P : _ -> Prop,
      (forall net net' failed failed' out,
         @step_f _ _ failure_params (failed, net) (failed', net') out ->
         P net ->
         P net') ->
      (forall net net' failed failed' out,
         step_f (failed, net) (failed', net') out ->
         P (deghost net) ->
         P (deghost net')).
  Proof.
    intros. eauto using ghost_simulation_1.
  Qed.

  Theorem ghost_invariant_lower :
    forall P : _ -> Prop,
      (forall net net' failed failed' out,
         step_f (failed, net) (failed', net') out ->
         P (deghost net) ->
         P (deghost net')) ->
      (forall net net' failed failed' out,
         @step_f _ _ failure_params (failed, net) (failed', net') out ->
         P net ->
         P net').
  Proof.
    intros.
    apply ghost_simulation_2 with (gnet := reghost net) in H0.
    - break_exists. intuition. subst.
      eapply H; eauto.
      rewrite reghost_deghost_partial_inverses.
      auto.
    - eauto using reghost_deghost_partial_inverses.
  Qed.

End GhostVars.

Class MsgGhostFailureParams `(P : FailureParams) :=
  {
    ghost_msg : Type;
    ghost_msg_eq_dec : forall x y : ghost_msg, {x = y} + {x <> y} ;
    ghost_msg_default : ghost_msg ;
    write_ghost_msg :
      name -> data -> ghost_msg
  }.

Section MsgGhostVars.
  Context {base_params : BaseParams}.
  Context {multi_params : MultiParams base_params}.
  Context {failure_params : FailureParams multi_params}.
  Context {params : MsgGhostFailureParams failure_params}.

  Definition add_ghost_msg (me : name) (st : data) (ps : list (name * msg)) :
                                                      list (name * (ghost_msg * msg)) :=
    map (fun m => (fst m, (write_ghost_msg me st, snd m))) ps.

  Definition mgv_refined_net_handlers me src (m : ghost_msg * msg) st :=
    let '(out, st', ps) :=
        net_handlers me src (snd m) st in
    (out, st', add_ghost_msg me st ps).

  Definition mgv_refined_input_handlers me inp st :=
    let '(out, st', ps) :=
        input_handlers me inp st in
    (out, st', add_ghost_msg me st ps).

  Definition mgv_msg_eq_dec :
    forall x y : ghost_msg * msg, {x = y} + {x <> y}.
  Proof.
    intros.
    decide equality; auto using msg_eq_dec, ghost_msg_eq_dec.
  Qed.

  Instance mgv_refined_base_params : BaseParams :=
    {
      data := data ;
      input := input ;
      output := output
    }.

  Instance mgv_refined_multi_params : MultiParams _ :=
    {
      name := name ;
      msg := (ghost_msg * msg) ;
      msg_eq_dec := mgv_msg_eq_dec ;
      name_eq_dec := name_eq_dec ;
      nodes := nodes ;
      all_names_nodes := all_names_nodes ;
      no_dup_nodes := no_dup_nodes ;
      init_handlers := init_handlers;
      net_handlers := mgv_refined_net_handlers ;
      input_handlers := mgv_refined_input_handlers
    }.
  
  Instance mgv_refined_failure_params : FailureParams _ :=
    {
      reboot := (@reboot base_params multi_params failure_params)
    }.

  Definition mgv_deghost_packet p :=
    @mkPacket _ multi_params
              (@pSrc _ mgv_refined_multi_params p)
              (pDst p)
              (snd (pBody p)).

  Definition mgv_deghost (net : @network _ mgv_refined_multi_params) : (@network _ multi_params).
    refine (@mkNetwork _ multi_params
                       (map mgv_deghost_packet
                          (nwPackets net))
                       _
           ).
    intros.
    destruct net.
    concludes.
    auto.
  Defined.

  Arguments mgv_deghost_packet /_.


  Require Import FunctionalExtensionality.

  Ltac workhorse :=
    try match goal with
        | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal
      end;
    try match goal with
        | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros
      end;
      repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => invc H
             end;
      repeat (simpl in *; subst);
      repeat rewrite map_app;
      repeat rewrite map_map.

  Theorem mgv_ghost_simulation_1 :
    forall net net' failed failed' out,
      @step_f _ _ mgv_refined_failure_params (failed, net) (failed', net') out ->
      @step_f _ _ failure_params (failed, mgv_deghost net) (failed', mgv_deghost net') out.
  Proof.
    intros.
    invcs H;
      unfold mgv_refined_net_handlers,
             mgv_refined_input_handlers,
             reboot,
             add_ghost_msg,
             mgv_deghost
               in *;
      workhorse;
    [(match goal with
          [ p : packet |- _ ] =>
            assert (pDst p = pDst (mgv_deghost_packet p)) by
              (destruct p; simpl in *; solve_by_inversion);
          repeat find_rewrite
      end);
      econstructor 1
      | econstructor 2
      | econstructor 3
      | econstructor 4
      | econstructor 5
      | econstructor 6
      ]; simpl; eauto;
      workhorse;
      congruence.
  Qed.

  Definition mgv_ghost_packet p :=
    @mkPacket _ mgv_refined_multi_params
              (@pSrc _ multi_params p)
              (pDst p)
              (ghost_msg_default, pBody p).


  Definition mgv_reghost (net : @network _ multi_params) : @network _ mgv_refined_multi_params.
    refine (@mkNetwork _ mgv_refined_multi_params
                       (map mgv_ghost_packet
                          (nwPackets net))
                       _
           ).
    intros.
    destruct net.
    concludes.
    auto.
  Defined.

  Arguments mgv_ghost_packet /_.

  Lemma mgv_reghost_deghost_partial_inverses :
    forall net,
      mgv_deghost (mgv_reghost net) = net.
  Proof.
    destruct net. unfold mgv_deghost, mgv_reghost. simpl in *. f_equal.
    rewrite map_map. map_id.
  Qed.

  Lemma map_partition :
    forall A B p l (x : B) p' (f : A -> B),
      map f l = (p ++ x :: p') ->
      exists ap a ap',
        l = ap ++ a :: ap' /\
        map f ap = p /\
        f a = x /\
        map f ap' = p'.
  Proof.
    induction p; intros; intuition; simpl in *.
    - destruct l; simpl in *; try congruence.
      find_inversion.
      exists [],a,l. simpl. auto.
    - destruct l; simpl in *; try congruence.
      find_inversion.
      find_apply_hyp_hyp.
      break_exists_name ap.
      break_exists_name a.
      break_exists_name ap'.
      intuition.
      exists (a0 :: ap), a, ap'. simpl.
      repeat find_rewrite. intuition.
  Qed.

  Theorem mgv_ghost_simulation_2 :
    forall net net' failed failed' out gnet,
      @step_f _ _ failure_params (failed, net) (failed', net') out ->
      mgv_deghost gnet = net ->
      exists gnet',
        step_f (failed, gnet) (failed', gnet') out /\
        mgv_deghost gnet' = net'.
  Proof.
    intros.
    invcs H.
    - repeat break_match. simpl in *.
      find_apply_lem_hyp map_partition.
      break_exists_name xs'.
      break_exists_name p'.
      break_exists_name ys'.
      intuition. 
      exists {| nwPackets := (@send_packets _ mgv_refined_multi_params (pDst p)
                                       (add_ghost_msg (pDst p) (nwState0 (pDst p)) l))
                          ++ xs' ++ ys';
           nwState := update nwState0 (pDst p) d |}.
      intuition.
      + simpl in *.
        subst.
        eapply (@SF_deliver _ _ mgv_refined_failure_params); simpl in *; eauto.
        unfold mgv_refined_net_handlers;
           repeat break_match; subst; simpl in *; repeat find_rewrite;
           find_inversion; auto.
      + simpl.
        unfold mgv_deghost.
        subst.
        simpl in *.
        unfold add_ghost_msg.
        map_crush. auto.
    - repeat break_match. subst. simpl in *.
      intuition.
      exists {| nwPackets := (@send_packets _ mgv_refined_multi_params h
                                       (add_ghost_msg h (nwState0 h) l))
                          ++ nwPackets0;
           nwState := update nwState0 h d |}.
      intuition.
      + simpl in *. 
        eapply (@SF_input _ _ mgv_refined_failure_params); simpl in *; eauto.
        unfold mgv_refined_input_handlers;
           repeat break_match; subst; simpl in *; repeat find_rewrite;
           find_inversion; auto.
      + simpl.
        unfold mgv_deghost.
        subst.
        simpl in *.
        unfold add_ghost_msg.
        map_crush. auto.
    - find_apply_lem_hyp map_partition.
      break_exists_name xs'.
      break_exists_name p'.
      break_exists_name ys'.
      intuition.
      exists {| nwPackets := xs' ++ ys';
           nwState := fun h => nwState gnet h |}.
      intuition.
      + eapply (@SF_drop _ _ mgv_refined_failure_params); simpl in *; eauto.
      + break_match.
        unfold mgv_deghost. simpl.
        f_equal.
        subst.
        map_crush. auto.
    - find_apply_lem_hyp map_partition.
      break_exists_name xs'.
      break_exists_name p'.
      break_exists_name ys'.
      intuition.
      exists {| nwPackets := p' :: xs' ++ p' :: ys';
           nwState := fun h => nwState gnet h |}.
      intuition.
      + eapply (@SF_dup _ _ mgv_refined_failure_params); simpl in *; eauto.
      + break_match.
        unfold mgv_deghost. simpl.
        f_equal.
        subst.
        map_crush. auto.
    - (exists gnet). intuition.
      apply (@SF_fail _ _ mgv_refined_failure_params).
    - (exists {| nwPackets := nwPackets gnet;
            nwState := update (nwState gnet) h (reboot (nwState gnet h))
         |}).
      intuition.
      + eapply (@SF_reboot _ _ mgv_refined_failure_params); eauto.
        f_equal. simpl in *. apply functional_extensionality.
         intros. break_if; congruence.
      + unfold mgv_deghost. simpl in *.  f_equal.
        break_match. 
        apply functional_extensionality. intros.
        repeat break_match; simpl in *; subst; auto.
  Qed.

  Theorem mgv_ghost_invariant_lift :
    forall P : _ -> Prop,
      (forall net net' failed failed' out,
         @step_f _ _ failure_params (failed, net) (failed', net') out ->
         P net ->
         P net') ->
      (forall net net' failed failed' out,
         step_f (failed, net) (failed', net') out ->
         P (mgv_deghost net) ->
         P (mgv_deghost net')).
  Proof.
    intros. eauto using mgv_ghost_simulation_1.
  Qed.

  Theorem mgv_ghost_invariant_lower :
    forall P : _ -> Prop,
      (forall net net' failed failed' out,
         step_f (failed, net) (failed', net') out ->
         P (mgv_deghost net) ->
         P (mgv_deghost net')) ->
      (forall net net' failed failed' out,
         @step_f _ _ failure_params (failed, net) (failed', net') out ->
         P net ->
         P net').
  Proof.
    intros.
    apply mgv_ghost_simulation_2 with (gnet := mgv_reghost net) in H0.
    - break_exists. intuition. subst.
      eapply H; eauto.
      rewrite mgv_reghost_deghost_partial_inverses.
      auto.
    - eauto using mgv_reghost_deghost_partial_inverses.
  Qed.

End MsgGhostVars.
Arguments deghost_packet /_ _ _ _ _.
Arguments ghost_packet /_ _ _ _ _.

Arguments mgv_deghost_packet /_ _ _ _ _.
Arguments mgv_ghost_packet /_ _ _ _ _.
