Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import StructTact.Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import FunctionalExtensionality.
Require Import Simulations.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

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
  destruct nwState. auto.
Defined.

Arguments deghost_packet /_.

Definition deghost_prop I (failed_net : list name * network) : Prop :=
  I ((fst failed_net), deghost (snd failed_net)).

Instance refined_base_params_tot_map : BaseParamsTotMap refined_base_params base_params :=
  {
    tot_map_data := snd ;
    tot_map_input := id ;
    tot_map_output := id
  }.

Instance refined_multi_params_tot_map : MultiParamsTotMap refined_base_params_tot_map refined_multi_params multi_params :=
  {
    tot_map_msg := id ;
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

Lemma ghost_tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n.
Proof. by []. Qed.

Lemma ghost_tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n.
Proof. by []. Qed.

Lemma ghost_eq_net_handlers_eq : 
  forall me src m st,
    tot_mapped_net_handlers me src m st = 
    net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st).
Proof.
move => me src m st.
rewrite /tot_mapped_net_handlers /= /refined_net_handlers /= /tot_map_name_msgs /= /id /=.
repeat break_let.
move {p0 Heqp1 p Heqp2}.
inversion Heqp; subst.
rewrite /=.
rewrite -/id.
rewrite map_id.
by rewrite map_fst_snd_id.
Qed.

Lemma ghost_eq_input_handlers_eq : forall me inp st,
  tot_mapped_input_handlers me inp st = input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st).
Proof.
move => me inp st.
rewrite /tot_mapped_input_handlers /=.
repeat break_let.
rewrite map_id.
rewrite /refined_input_handlers in Heqp.
repeat break_let.
rewrite /id /= Heqp1.
inversion Heqp; subst.
rewrite /= /tot_map_name_msgs /= /id /=.
by rewrite map_fst_snd_id.
Qed.

Lemma ghost_tot_map_output_injective : 
  forall o o', tot_map_output o = tot_map_output o' -> o = o'.
Proof. by []. Qed.

Lemma ghost_tot_mapped_reboot_eq : forall d,
  tot_map_data (reboot d) = reboot (tot_map_data d).
Proof. by []. Qed.

Lemma map_id_tr :
forall out,
map (fun e : name * (input + list output) =>
                 let (n, s) := e in
                 match s with
                 | inl io => (n, inl io)
                 | inr lo => (n, inr (map id lo))
                 end) out = out.
elim => //.
move => tr l IH.
rewrite /= IH.
break_let.
case: s Heqp => //=.
move => out H_eq.
by rewrite map_id.
Qed.

Theorem ghost_simulation_1 :
  forall net net' failed failed' out,
    @step_f _ _ refined_failure_params (failed, net) (failed', net') out ->
    @step_f _ _ failure_params (failed, deghost net) (failed', deghost net') out.
Proof.
have H_sim := step_f_tot_mapped_simulation_1 ghost_tot_map_name_inv_inverse ghost_tot_map_name_inverse_inv ghost_eq_net_handlers_eq ghost_eq_input_handlers_eq ghost_tot_mapped_reboot_eq.
move => net net' failed failed' out H_step.
apply H_sim in H_step.
rewrite /tot_map_name /tot_map_net /= 2!map_id /id /= in H_step.
rewrite /tot_map_trace_occ /= /id /= in H_step.
rewrite /tot_map_packet /= /id /= in H_step.
rewrite /deghost /=.
rewrite -/id map_id_tr in H_step.
move: H_step.
set fp := fun p : packet => _.
set fp' := fun p : packet => _.
have H_eq: fp = fp' by rewrite /fp /fp'; apply functional_extensionality; case => /= src dst m.
rewrite H_eq {H_eq fp}.
set fs1 := fun n => _.
set fs2 := fun n => _.
set fs1' := fun n => _.
set fs2' := fun n => _.
have H_eq: fs1 = fs1' by rewrite /fs1 /fs1' {fs1 fs1'}; apply functional_extensionality => n; case: net.
rewrite H_eq {H_eq fs1}.
have H_eq: fs2 = fs2' by rewrite /fs2 /fs2' {fs2 fs2'}; apply functional_extensionality => n; case: net'.
by rewrite H_eq {H_eq fs2}.
Qed.

Theorem ghost_simulation_2 :
  forall net net' failed failed' out gnet,
    @step_f _ _ failure_params (failed, net) (failed', net') out ->
    deghost gnet = net ->
    exists gnet',
      step_f (failed, gnet) (failed', gnet') out /\
      deghost gnet' = net'.
Proof.
have H_sim := step_f_tot_mapped_simulation_2 ghost_tot_map_name_inv_inverse ghost_tot_map_name_inverse_inv ghost_eq_net_handlers_eq ghost_eq_input_handlers_eq ghost_tot_map_output_injective ghost_tot_mapped_reboot_eq.
move => net net' failed failed' out gnet H_step H_eq.
apply (H_sim _ _ _ _ _ gnet failed failed' out) in H_step.
- move: H_step => [gnet' [H_step H_eq_net]].
  exists gnet'.
  split => //.
  rewrite -H_eq_net {H_step H_eq_net}.
  rewrite /deghost /tot_map_net /= /id /= /tot_map_packet /= /id /=.
  set nwPf1 := fun p : packet => _.
  set nwPf2 := fun p : packet => _.
  have H_eq_p: nwPf1 = nwPf2 by rewrite /nwPf1 /nwPf2 {nwPf1 nwPf2}; apply functional_extensionality; case.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2 by rewrite /nwS1 /nwS2 {nwS1 nwS2}; apply functional_extensionality => n; case: gnet'.
  by rewrite H_eq_p H_eq_s.
- rewrite /tot_map_net /= /id /= /tot_map_packet /= /id /=.
  move: H_eq.
  rewrite /deghost /=.
  set nwPf1 := fun p : packet => _.
  set nwPf2 := fun p : packet => _.
  have H_eq_p: nwPf1 = nwPf2 by rewrite /nwPf1 /nwPf2 {nwPf1 nwPf2}; apply functional_extensionality; case.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2 by rewrite /nwS1 /nwS2 {nwS1 nwS2}; apply functional_extensionality => n; case: gnet.
  by rewrite H_eq_p H_eq_s.
- by rewrite /tot_map_name /= map_id.
- by rewrite /tot_map_name /= map_id.
- move {H_step}.
  elim: out => //.
  case => n t out IH.
  case: t => /=.
    move => inp.
    rewrite /id /=.
    by rewrite IH.
  move => out'.
  by rewrite {1}/id map_id /= IH.
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
  exact (ghost_init, nwState).
Defined.

Arguments ghost_packet /_.

Lemma reghost_deghost_partial_inverses :
  forall net,
    deghost (reghost net) = net.
Proof.
  destruct net. unfold deghost, reghost. simpl in *. f_equal.
  rewrite map_map. map_id.
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
  (out, st', add_ghost_msg me st' ps).

Definition mgv_refined_input_handlers me inp st :=
  let '(out, st', ps) :=
      input_handlers me inp st in
  (out, st', add_ghost_msg me st' ps).

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

Instance mgv_refined_base_params_tot_map : BaseParamsTotMap mgv_refined_base_params base_params :=
  {
    tot_map_data := id ;
    tot_map_input := id ;
    tot_map_output := id
  }.

Instance mgv_refined_multi_params_tot_map : MultiParamsTotMap mgv_refined_base_params_tot_map mgv_refined_multi_params multi_params :=
  {
    tot_map_msg := snd ;
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

Lemma mgv_tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n.
Proof. by []. Qed.

Lemma mgv_tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n.
Proof. by []. Qed.

Lemma mgv_eq_net_handlers_eq : 
  forall me src m st,
    tot_mapped_net_handlers me src m st = 
    net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st).
Proof.
move => me src m st.
rewrite /tot_mapped_net_handlers /= /mgv_refined_net_handlers /= /tot_map_name_msgs /= /id /=.
repeat break_let.
rewrite -/id map_id.
inversion Heqp; subst.
move {Heqp0 Heqp}.
rewrite /add_ghost_msg /=.
elim: l0 => //.
case => n m' l IH.
rewrite /=.
injection IH; subst.
move => IH'.
by rewrite IH'.
Qed.

Lemma mgv_eq_input_handlers_eq : forall me inp st,
  tot_mapped_input_handlers me inp st = input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st).
Proof.
move => me inp st.
rewrite /tot_mapped_input_handlers /=.
repeat break_let.
rewrite map_id /id /=.
rewrite /mgv_refined_input_handlers in Heqp.
repeat break_let.
inversion Heqp; subst.
rewrite /= /tot_map_name_msgs /= /id /=.
move {Heqp1 Heqp}.
elim: l1 => //.
case => n m l.
rewrite /=.
move => IH.
injection IH; subst.
move => IH'.
by rewrite IH'.
Qed.

Lemma mgv_tot_map_output_injective : 
  forall o o', tot_map_output o = tot_map_output o' -> o = o'.
Proof. by []. Qed.

Lemma mgv_tot_mapped_reboot_eq : forall d,
  tot_map_data (reboot d) = reboot (tot_map_data d).
Proof. by []. Qed.

Lemma mgv_map_id_tr :
forall out,
map (fun e : name * (input + list output) =>
                 let (n, s) := e in
                 match s with
                 | inl io => (n, inl io)
                 | inr lo => (n, inr (map id lo))
                 end) out = out.
elim => //.
move => tr l IH.
rewrite /= IH.
break_let.
case: s Heqp => //=.
move => out H_eq.
by rewrite map_id.
Qed.

Theorem mgv_ghost_simulation_1 :
  forall net net' failed failed' out,
    @step_f _ _ mgv_refined_failure_params (failed, net) (failed', net') out ->
    @step_f _ _ failure_params (failed, mgv_deghost net) (failed', mgv_deghost net') out.
Proof.
have H_sim := step_f_tot_mapped_simulation_1 mgv_tot_map_name_inv_inverse mgv_tot_map_name_inverse_inv mgv_eq_net_handlers_eq mgv_eq_input_handlers_eq mgv_tot_mapped_reboot_eq.
move => net net' failed failed' out H_step.
apply H_sim in H_step.
rewrite /tot_map_name /tot_map_net /= 2!map_id /id /= in H_step.
rewrite /tot_map_trace_occ /= /id /= in H_step.
rewrite /tot_map_packet /= /id /= in H_step.
rewrite /mgv_deghost /=.
rewrite -/id mgv_map_id_tr in H_step.
move: H_step.
set fp := fun p : packet => _.
set fp' := fun p : packet => _.
have H_eq: fp = fp' by rewrite /fp /fp'; apply functional_extensionality; case => /= src dst m.
rewrite H_eq {H_eq fp}.
set fs1 := fun n => _.
set fs2 := fun n => _.
set fs1' := fun n => _.
set fs2' := fun n => _.
have H_eq: fs1 = fs1' by rewrite /fs1 /fs1' {fs1 fs1'}; apply functional_extensionality => n; case: net.
rewrite H_eq {H_eq fs1}.
have H_eq: fs2 = fs2' by rewrite /fs2 /fs2' {fs2 fs2'}; apply functional_extensionality => n; case: net'.
by rewrite H_eq {H_eq fs2}.
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

Theorem mgv_ghost_simulation_2 :
  forall net net' failed failed' out gnet,
    @step_f _ _ failure_params (failed, net) (failed', net') out ->
    mgv_deghost gnet = net ->
    exists gnet',
      step_f (failed, gnet) (failed', gnet') out /\
      mgv_deghost gnet' = net'.
Proof.
have H_sim := step_f_tot_mapped_simulation_2 mgv_tot_map_name_inv_inverse mgv_tot_map_name_inverse_inv mgv_eq_net_handlers_eq mgv_eq_input_handlers_eq mgv_tot_map_output_injective mgv_tot_mapped_reboot_eq.
move => net net' failed failed' out gnet H_step H_eq.
apply (H_sim _ _ _ _ _ gnet failed failed' out) in H_step.
- move: H_step => [gnet' [H_step H_eq_net]].
  exists gnet'.
  split => //.
  rewrite -H_eq_net {H_step H_eq_net}.
  rewrite /mgv_deghost /tot_map_net /= /id /= /tot_map_packet /= /id /=.
  set nwPf1 := fun p : packet => _.
  set nwPf2 := fun p : packet => _.
  have H_eq_p: nwPf1 = nwPf2 by rewrite /nwPf1 /nwPf2 {nwPf1 nwPf2}; apply functional_extensionality; case.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2 by rewrite /nwS1 /nwS2 {nwS1 nwS2}; apply functional_extensionality => n; case: gnet'.
  by rewrite H_eq_p H_eq_s.
- rewrite -H_eq {H_step H_eq}.
  rewrite /mgv_deghost /tot_map_net /= /id /= /tot_map_packet /= /id /=.
  set nwPf1 := fun p : packet => _.
  set nwPf2 := fun p : packet => _.
  have H_eq_p: nwPf1 = nwPf2 by rewrite /nwPf1 /nwPf2 {nwPf1 nwPf2}; apply functional_extensionality; case.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2 by rewrite /nwS1 /nwS2 {nwS1 nwS2}; apply functional_extensionality => n; case: gnet.
  by rewrite H_eq_p H_eq_s.
- by rewrite /tot_map_name /= map_id.
- by rewrite /tot_map_name /= map_id.
- move {H_step}.
  elim: out => //.
  case => n t out IH.
  case: t => /=.
    move => inp.
    rewrite /id /=.
    by rewrite IH.
  move => out'.
  by rewrite {1}/id map_id /= IH.
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
