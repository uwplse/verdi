Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.

Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class BaseParamsTotMap (P0 : BaseParams) (P1 : BaseParams) := 
  {
    tot_map_data : @data P0 -> @data P1 ;
    tot_map_input : @input P0 -> @input P1 ;
    tot_map_output : @output P0 -> @output P1
  }.

Class MultiParamsTotMap
 (B0 : BaseParams) (B1 : BaseParams) 
 (B : BaseParamsTotMap B0 B1)
 (P0 : MultiParams B0) (P1 : MultiParams B1)  :=
{
   tot_map_msg : @msg B0 P0 -> @msg B1 P1 ;
   tot_map_name : @name B0 P0 -> @name B1 P1 ;
   tot_map_name_inv : @name B1 P1 -> @name B0 P0
}.

Section TotMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotMap base_fst base_snd}.
Context {multi_map : MultiParamsTotMap base_map multi_fst multi_snd}.

Hypothesis tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n.

Hypothesis tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n.

Hypothesis tot_init_handlers_eq : forall n, tot_map_data (init_handlers n) = init_handlers (tot_map_name n).

Definition tot_map_name_msgs :=
  map (fun nm => (tot_map_name (fst nm), tot_map_msg (snd nm))).

Definition tot_mapped_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).

Hypothesis tot_net_handlers_eq : forall me src m st,
  tot_mapped_net_handlers me src m st = 
  net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st).

Definition tot_mapped_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).

Hypothesis tot_input_handlers_eq : forall me inp st,
  tot_mapped_input_handlers me inp st = input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st).

Hypothesis tot_map_output_injective : 
  forall o o', tot_map_output o = tot_map_output o' -> o = o'.

Lemma tot_map_name_injective : 
forall n n', tot_map_name n = tot_map_name n' -> n = n'.
Proof.
move => n n'.
case (name_eq_dec n n') => H_dec //.
move => H_eq.
rewrite -(tot_map_name_inv_inverse n) in H_dec.
rewrite H_eq in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Definition tot_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) :=
match e with
| (n, inl io) => (tot_map_name n, inl (tot_map_input io))
| (n, inr lo) => (tot_map_name n, inr (map tot_map_output lo))
end.

Definition tot_map_packet (p : @packet base_fst multi_fst)  :=
match p with
| mkPacket src dst m =>
  mkPacket (tot_map_name src) (tot_map_name dst) (tot_map_msg m)
end.

Definition tot_map_net (net : @network _ multi_fst) : @network _ multi_snd :=
mkNetwork (map tot_map_packet net.(nwPackets)) (fun n => tot_map_data (net.(nwState) (tot_map_name_inv n))).

Lemma tot_map_update_eq :
  forall f d h,
    (fun n : name => tot_map_data (update f h d (tot_map_name_inv n))) =
    update (fun n : name => tot_map_data (f (tot_map_name_inv n))) (tot_map_name h) (tot_map_data d).
Proof.
move => net d h.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' //.
  rewrite -H_dec in H_dec'.
  by rewrite tot_map_name_inverse_inv in H_dec'.
rewrite H_dec' in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Corollary tot_map_update_packet_eq :
forall f p d,
  (fun n : name => tot_map_data (update f (pDst p) d (tot_map_name_inv n))) =
  (update (fun n : name => tot_map_data (f (tot_map_name_inv n))) (pDst (tot_map_packet p)) (tot_map_data d)).
Proof.
move => f. 
case => src dst m d.
exact: tot_map_update_eq.
Qed.

Lemma tot_map_packet_app_eq :
  forall l p ms ms',
    map tot_map_packet (map (fun m : name * msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l ++ ms ++ ms') = 
    map (fun m : name * msg => {| pSrc := pDst (tot_map_packet p); pDst := fst m; pBody := snd m |}) (tot_map_name_msgs l) ++ map tot_map_packet ms ++ map tot_map_packet ms'.
Proof.
move => l; case => src dst m ms ms'.
rewrite 2!map_app.
elim: l => //=.
case => /= n m' l IH.
by rewrite IH.
Qed.

Lemma tot_map_packet_eq :
  forall l l' h,
    map tot_map_packet (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l ++ l') =
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (tot_map_name_msgs l) ++ map tot_map_packet l'.
Proof.
elim => //=.
case => n m l IH l' h.
by rewrite IH.
Qed.

Lemma tot_init_handlers_fun_eq : 
    init_handlers = fun n : name => tot_map_data (init_handlers (tot_map_name_inv n)).
Proof.
apply functional_extensionality => n.
rewrite tot_init_handlers_eq.
by rewrite tot_map_name_inverse_inv.
Qed.

Lemma tot_map_trace_occ_inv : 
  forall tr n ol,
    map tot_map_trace_occ tr = [(n, inr ol)] -> 
    exists n', exists lo, tr = [(n', inr lo)] /\ tot_map_name n' = n /\ map tot_map_output lo = ol.
Proof.
case => //=.
case.
move => n ol tr n' lo H_eq.
case: tr H_eq => //=.
case: ol => //=.
move => out H_eq.
exists n; exists out.
split => //.
by inversion H_eq.
Qed.

Lemma tot_map_trace_occ_in_inv : 
  forall tr h inp out,
    map tot_map_trace_occ tr = [(h, inl inp); (h, inr out)] -> 
    exists h', exists inp', exists out', tr = [(h', inl inp'); (h', inr out')] /\ 
      tot_map_name h' = h /\ map tot_map_output out' = out /\ tot_map_input inp' = inp.
Proof.
case => //=.
case.
move => h.
case => //.
move => inp.
case => //.
case.
move => h'.
case => //.
move => out.
case => //=.
move => h0.
move => inp' out' H_eq.
inversion H_eq; subst.
apply tot_map_name_injective in H2.
rewrite H2.
by exists h; exists inp; exists out.
Qed.

Theorem step_m_tot_mapped_simulation_1 :
  forall net net' tr,
    @step_m _ multi_fst net net' tr ->
    @step_m _ multi_snd (tot_map_net net) (tot_map_net net') (map tot_map_trace_occ tr).
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  rewrite /tot_map_trace_occ /=.
  have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by case: p H_eq H_hnd H_eq' => src dst m H_eq H_hnd H_eq'.
  apply (@SM_deliver _ _ _ _ _ (map tot_map_packet ms) (map tot_map_packet ms') (map tot_map_output out) (tot_map_data d) (tot_map_name_msgs l)).
  * by rewrite /tot_map_net /= H_eq /= map_app.
  * rewrite /=.
    case: p H_eq H_hnd H_eq' => /= src dst m H_eq H_hnd H_eq'.
    have H_q := tot_net_handlers_eq dst src m (nwState net dst).
    rewrite /tot_mapped_net_handlers in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= H_eq' /= /tot_map_net /=.
    rewrite -tot_map_update_packet_eq.
    by rewrite tot_map_packet_app_eq.
- move => h net net' out inp d l H_hnd H_eq.
  apply (@SM_input _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
    rewrite /=.
    have H_q := tot_input_handlers_eq h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  rewrite /= H_eq /= /tot_map_net /=.
  rewrite -tot_map_update_eq.
  by rewrite tot_map_packet_eq.
Qed.

Corollary step_m_tot_mapped_simulation_star_1 :
  forall net tr,
    @step_m_star _ multi_fst step_m_init net tr ->
    @step_m_star _ multi_snd step_m_init (tot_map_net net) (map tot_map_trace_occ tr).
Proof.
move => net tr H_step.
remember step_m_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_m_init /= /tot_map_net /=.
  rewrite tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_m_tot_mapped_simulation_1 in H.
rewrite map_app.
have H_trans := refl_trans_1n_trace_trans IHH_step1.
apply: H_trans.
rewrite (app_nil_end (map _ _)).
apply: (@RT1nTStep _ _ _ _ (tot_map_net x'')) => //.
exact: RT1nTBase.
Qed.

Theorem step_m_tot_mapped_simulation_2 :
  forall net net' out mnet mout,
      @step_m _ multi_snd net net' out ->
      tot_map_net mnet = net ->
      map tot_map_trace_occ mout = out ->
      exists mnet',
        @step_m _ multi_fst mnet mnet' mout /\
        tot_map_net mnet' = net'.
Proof.
move => net net' out mnet mout H_step H_eq H_eq'.
invcs H_step.
- case: p H4 H H0 => /= src dst m H4 H H0.
  rewrite /tot_map_net /=.
  case: mnet H H0 => /= pks sts H_eq H_hnd.
  have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H_eq.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (pDst p) (pSrc p) (pBody p) (sts (pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (pDst p) l' ++ pks1 ++ pks2 ; nwState := update sts (pDst p) d' |}.
  split.
  * have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H4).
    rewrite H_eq_mout.
    have H_eq_dst: n' = pDst p.
      rewrite -(tot_map_name_inv_inverse n').
      rewrite H_eq_n.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd'.
      rewrite /=.
      rewrite /= in H0.
      inversion H0.
      by rewrite tot_map_name_inv_inverse.
    rewrite H_eq_dst.
    apply (@SM_deliver _ _ _ _ _ pks1 pks2 _ d' l') => //=.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := tot_net_handlers_eq (pDst p) (pSrc p) (pBody p) (sts (pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H2 H3 H5 in H_eq_hnd.
    rewrite -{1}H_eq_dst H_eq_n in H_eq_hnd.
    rewrite -H_eq_dst in H_eq_hnd.
    rewrite -(tot_map_name_inv_inverse n') H_eq_n in H_eq_hnd.
    move {Heqp1 Heqp0 H_hnd'}.
    have H_eq_src: tot_map_name (pSrc p) = src.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd.
      rewrite /=.
      rewrite /= in H0.
      by inversion H0.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: tot_map_msg (pBody p) = m.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd.
      rewrite /=.
      rewrite /= in H0.
      by inversion H0.
    rewrite H_eq_body H_hnd in H_eq_hnd.
    inversion H_eq_hnd.
    rewrite -H_eq_lo in H6.
    symmetry.
    move: H6.
    apply map_eq_inv_eq.
    exact: tot_map_output_injective.
  * rewrite /=.
    rewrite /update /=.
    have H_eq_dst: tot_map_name (pDst p) = dst.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd'.
      by inversion H0.
    have H_eq_src: tot_map_name (pSrc p) = src.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' H_eq_dst => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd' H_eq_dst.
      by inversion H0.
    have H_eq_body: tot_map_msg (pBody p) = m.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_src H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_src H_hnd'.
      by inversion H0.
    rewrite 2!map_app.
    have H_eq_hnd := tot_net_handlers_eq (pDst p) (pSrc p) (pBody p) (sts (pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H_hnd.
    rewrite H_hnd in H_eq_hnd.
    inversion H_eq_hnd.
    rewrite H2 in H6.
    rewrite H3 in H7.
    rewrite H5 in H8.
    rewrite H3 H5.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {H_hnd' H5 H8 nwP1 nwP2}.
      elim: l' => //=.
      case => /= n' m' l' IH.
      rewrite IH.
      by rewrite H_eq_dst.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      rewrite -H_eq_dst.
      case (name_eq_dec _ _) => H_dec.
        rewrite -H_dec.
        rewrite tot_map_name_inverse_inv.
        by case (name_eq_dec _ _).
      case (name_eq_dec _ _) => H_dec' //.
      rewrite H_dec' in H_dec.
      by rewrite tot_map_name_inv_inverse in H_dec.
    by rewrite H_eq_sw.
- rewrite /tot_map_net /=.
  case: mnet H => /= pks sts H_hnd.
  have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H3).
  have H_q := tot_input_handlers_eq h' inp' (sts h').
  rewrite /tot_mapped_input_handlers in H_q.
  repeat break_let.
  rewrite H_eq_n H_eq_inp in H_q.
  rewrite -{2}H_eq_n tot_map_name_inv_inverse in H_hnd.
  rewrite H_hnd in H_q.
  inversion H_q.
  rewrite -H_eq_out in H0.
  rewrite H1 H2.
  exists ({| nwPackets := send_packets h' l0 ++ pks ; nwState := update sts h' d0 |}).
  split.
  * rewrite H_eq_mout.
    apply (@SM_input _ _ _ _ _ _ _ d0 l0) => //.
    rewrite /= Heqp.
    suff H_suff: l1 = out' by rewrite H_suff.
    move: H0.
    apply map_eq_inv_eq.
    exact: tot_map_output_injective.
  * rewrite /= map_app.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) l.
    set nwS1 := fun _ => _.
    set nwS2 := update _ _ _.
    have H_eq_nwp: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {Heqp H_q nwP1 nwP2}.
      rewrite -H2 {H2}.
      elim: l0 => //=.
      case => /= n m l0 IH.
      by rewrite H_eq_n IH.
    have H_eq_nws: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      rewrite /update /=.
      apply functional_extensionality => n.
      rewrite -H_eq_n -H1.
      case (name_eq_dec _ _) => H_dec.
        case (name_eq_dec _ _) => H_dec' //.
        by rewrite -H_dec tot_map_name_inverse_inv in H_dec'.
      case (name_eq_dec _ _) => H_dec' //.
      by rewrite H_dec' tot_map_name_inv_inverse in H_dec.
    by rewrite H_eq_nwp H_eq_nws.
Qed.

Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.

Hypothesis tot_reboot_eq : forall d, tot_map_data (reboot d) = reboot (tot_map_data d).

Lemma not_in_failed_not_in :
  forall n failed,
    ~ In n failed ->
    ~ In (tot_map_name n) (map tot_map_name failed).
Proof.
move => n.
elim => //=.
move => n' failed IH H_in H_in'.
case: H_in' => H_in'.
  case: H_in.
  left.
  rewrite -(tot_map_name_inv_inverse n').
  rewrite H_in'.
  exact: tot_map_name_inv_inverse.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma in_failed_in :
  forall n failed,
    In n failed ->
    In (tot_map_name n) (map tot_map_name failed).
Proof.
move => n.
elim => //.
move => n' l IH H_in.
case: H_in => H_in.
  rewrite H_in.
  by left.
right.
exact: IH.
Qed.

Lemma remove_tot_map_eq :
  forall h failed,
    map tot_map_name (remove name_eq_dec h failed) =
    remove name_eq_dec (tot_map_name h) (map tot_map_name failed).
Proof.
move => h.
elim => //=.
move => n failed IH.
case (name_eq_dec _ _) => H_eq; case (name_eq_dec _ _) => H_eq' //.
- by rewrite H_eq in H_eq'.
- rewrite -(tot_map_name_inv_inverse h) in H_eq.
  rewrite H_eq' in H_eq.
  by rewrite tot_map_name_inv_inverse in H_eq.
- by rewrite /= IH.
Qed.

Lemma tot_map_reboot_eq :
forall h net,
    (fun n : name => 
      tot_map_data 
        (match name_eq_dec (tot_map_name_inv n) h with
         | left _ => reboot (nwState net (tot_map_name_inv n))
         | right _ => nwState net (tot_map_name_inv n)
        end)) =
    (fun nm : name =>
       match name_eq_dec nm (tot_map_name h) with
       | left _ => reboot (tot_map_data (nwState net (tot_map_name_inv nm)))
       | right _ => tot_map_data (nwState net (tot_map_name_inv nm))
       end).
Proof.
move => h net.
apply: functional_extensionality => n.
case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' //.
- rewrite -H_dec in H_dec'.
  by rewrite tot_map_name_inverse_inv in H_dec'.
- rewrite H_dec' in H_dec.
  by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Theorem step_f_tot_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_f _ _ fail_fst (failed, net) (failed', net') tr ->
    @step_f _ _ fail_snd (map tot_map_name failed, tot_map_net net) (map tot_map_name failed', tot_map_net net') (map tot_map_trace_occ tr).
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by case: p H3 H4 H6 => src dst m.
  apply (@SF_deliver _ _ _ _ _ _ _ (map tot_map_packet xs) (map tot_map_packet ys) _ (tot_map_data d) (tot_map_name_msgs l)).
  * by rewrite /tot_map_net /= H3 /= map_app.
  * case: p H3 H4 H6 => /= src dst m H3 H4 H6.
    exact: not_in_failed_not_in.
  * case: p H3 H4 H6 => /= src dst m H3 H4 H6.        
    have H_q := tot_net_handlers_eq dst src m (nwState net dst).
    rewrite /tot_mapped_net_handlers in H_q.
    rewrite H6 in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= -tot_map_update_packet_eq /=.
    rewrite /tot_map_net /=.
    by rewrite tot_map_packet_app_eq.
- apply (@SF_input _ _ _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /=.
    have H_q := tot_input_handlers_eq h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= in H_q.
    rewrite H5 in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= /tot_map_net /=.
    rewrite -tot_map_update_eq.
    by rewrite tot_map_packet_eq.
- apply (@SF_drop _ _ _ _ _ _ (tot_map_packet p) (map tot_map_packet xs) (map tot_map_packet ys)).
  * by rewrite /tot_map_net /= H4 map_app.
  * by rewrite /tot_map_net /= map_app.
- apply (@SF_dup _ _ _ _ _ _ (tot_map_packet p) (map tot_map_packet xs) (map tot_map_packet ys)).
  * by rewrite /tot_map_net /= H4 map_app.
  * by rewrite /tot_map_net /= map_app.
- exact: SF_fail.
- apply: (SF_reboot (tot_map_name h)).
  * exact: in_failed_in.
  * by rewrite remove_tot_map_eq.
  * rewrite /tot_map_net /=.
    by rewrite tot_map_reboot_eq.
Qed.

Corollary step_f_tot_mapped_simulation_star_1 :
  forall net failed tr,
    @step_f_star _ _ fail_fst step_f_init (failed, net) tr ->
    @step_f_star _ _ fail_snd step_f_init (map tot_map_name failed, tot_map_net net) (map tot_map_trace_occ tr).
Proof.
move => net failed tr H_step.
remember step_f_init as y in *.
have H_eq_f: failed = fst (failed, net) by [].
have H_eq_n: net = snd (failed, net) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_n {H_eq_n}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_f_init /= /step_m_init /tot_map_net /=.
  rewrite tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_f_tot_mapped_simulation_1 in H.
rewrite map_app.
have H_trans := refl_trans_1n_trace_trans IHH_step1.
apply: H_trans.
rewrite (app_nil_end (map tot_map_trace_occ _)).
apply (@RT1nTStep _ _ _ _ (map tot_map_name failed'', tot_map_net net'')) => //.
exact: RT1nTBase.
Qed.

Lemma map_eq_name_eq_eq :
  forall l l', map tot_map_name l = map tot_map_name l' -> l = l'.
Proof.
elim.
case => //=.
move => n l IH.
case => //=.
move => n' l' H_eq.
inversion H_eq.
apply tot_map_name_injective in H0.
by rewrite H0 (IH l').
Qed.

Theorem step_f_tot_mapped_simulation_2 :
  forall net net' failed failed' out mnet mfailed mfailed' mout,
      @step_f _ _ fail_snd (failed, net) (failed', net') out ->
      tot_map_net mnet = net ->
      map tot_map_name mfailed = failed ->
      map tot_map_name mfailed' = failed' ->
      map tot_map_trace_occ mout = out ->
      exists mnet',
        @step_f _ _ fail_fst (mfailed, mnet) (mfailed', mnet') mout /\
        tot_map_net mnet' = net'.
Proof.
move => net net' failed failed' out mnet mfailed mfailed' mout H_step H_eq_net H_eq_f H_eq_f' H_eq_out.
invcs H_step.
- case: p H4 H5 H3 H6 => /= src dst m H4 H5 H3 H6.
  rewrite /tot_map_net /=.
  case: mnet H3 H6 => /= pks sts H_eq H_hnd.
  have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H_eq.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (pDst p) (pSrc p) (pBody p) (sts (pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (pDst p) l' ++ pks1 ++ pks2 ; nwState := update sts (pDst p) d' |}.
  split.
  * have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H5).
    rewrite H_eq_mout.
    have H_eq_dst: n' = pDst p.
      rewrite -(tot_map_name_inv_inverse n').
      rewrite H_eq_n.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd'.
      rewrite /=.
      rewrite /= in H0.
      inversion H0.
      by rewrite tot_map_name_inv_inverse.
    rewrite H_eq_dst.
    apply map_eq_name_eq_eq in H1.
    rewrite H1.    
    apply (@SF_deliver _ _ _ _ _ _ _ pks1 pks2 _ d' l') => //=.
      rewrite -H_eq_dst.
      rewrite -H_eq_n in H4.
      move => H_in.
      by apply in_failed_in in H_in.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := tot_net_handlers_eq (pDst p) (pSrc p) (pBody p) (sts (pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H3 H6 H7 in H_eq_hnd.
    rewrite -{1}H_eq_dst H_eq_n in H_eq_hnd.
    rewrite -H_eq_dst in H_eq_hnd.
    rewrite -(tot_map_name_inv_inverse n') H_eq_n in H_eq_hnd.
    move {Heqp1 Heqp0 H_hnd'}.
    have H_eq_src: tot_map_name (pSrc p) = src.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd.
      rewrite /=.
      rewrite /= in H0.
      by inversion H0.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: tot_map_msg (pBody p) = m.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd.
      rewrite /=.
      rewrite /= in H0.
      by inversion H0.
    rewrite H_eq_body H_hnd in H_eq_hnd.
    inversion H_eq_hnd.
    rewrite -H_eq_lo in H8.
    symmetry.
    move: H8.
    apply map_eq_inv_eq.
    exact: tot_map_output_injective.
  * rewrite /=.
    rewrite /update /=.
    have H_eq_dst: tot_map_name (pDst p) = dst.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd'.
      by inversion H0.
    have H_eq_src: tot_map_name (pSrc p) = src.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' H_eq_dst => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd' H_eq_dst.
      by inversion H0.
    have H_eq_body: tot_map_msg (pBody p) = m.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_src H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_src H_hnd'.
      by inversion H0.
    rewrite 2!map_app.
    have H_eq_hnd := tot_net_handlers_eq (pDst p) (pSrc p) (pBody p) (sts (pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H_hnd.
    rewrite H_hnd in H_eq_hnd.
    inversion H_eq_hnd.
    rewrite H3 in H8.
    rewrite H6 in H9.
    rewrite H7 in H10.
    rewrite H6 H7.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {H_hnd' H7 H10 nwP1 nwP2}.
      elim: l' => //=.
      case => /= n' m' l' IH.
      rewrite IH.
      by rewrite H_eq_dst.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      rewrite -H_eq_dst.
      case (name_eq_dec _ _) => H_dec.
        rewrite -H_dec.
        rewrite tot_map_name_inverse_inv.
        by case (name_eq_dec _ _).
      case (name_eq_dec _ _) => H_dec' //.
      rewrite H_dec' in H_dec.
      by rewrite tot_map_name_inv_inverse in H_dec.
    by rewrite H_eq_sw.
- rewrite /tot_map_net /=.
  case: mnet H5 => /= pks sts H_hnd.
  have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H4).
  have H_q := tot_input_handlers_eq h' inp' (sts h').
  rewrite /tot_mapped_input_handlers in H_q.
  repeat break_let.
  rewrite H_eq_n H_eq_inp in H_q.
  rewrite -{2}H_eq_n tot_map_name_inv_inverse in H_hnd.
  rewrite H_hnd in H_q.
  inversion H_q.
  rewrite -H_eq_out in H0.
  rewrite H2 H5.
  apply map_eq_name_eq_eq in H1.
  rewrite -H1.
  rewrite -H1 in H3.
  exists ({| nwPackets := send_packets h' l0 ++ pks ; nwState := update sts h' d0 |}).
  split.
  * rewrite H_eq_mout.
    apply (@SF_input _ _ _ _ _ _ _ _ _ d0 l0) => //.      
      rewrite -H_eq_n in H3.
      move => H_in.
      by apply in_failed_in in H_in.
    rewrite /= Heqp.
    suff H_suff: l1 = out' by rewrite H_suff.
    move: H0.
    apply map_eq_inv_eq.
    exact: tot_map_output_injective.
  * rewrite /= map_app.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) l.
    set nwS1 := fun _ => _.
    set nwS2 := update _ _ _.
    have H_eq_nwp: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {Heqp H_q nwP1 nwP2}.
      rewrite -H5 {H5}.
      elim: l0 => //=.
      case => /= n m l0 IH.
      by rewrite H_eq_n IH.
    have H_eq_nws: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      rewrite /update /=.
      apply functional_extensionality => n.
      rewrite -H_eq_n -H2.
      case (name_eq_dec _ _) => H_dec.
        case (name_eq_dec _ _) => H_dec' //.
        by rewrite -H_dec tot_map_name_inverse_inv in H_dec'.
      case (name_eq_dec _ _) => H_dec' //.
      by rewrite H_dec' tot_map_name_inv_inverse in H_dec.
    by rewrite H_eq_nwp H_eq_nws.
- case: mout H2 => // H_eq_mout {H_eq_mout}.
  apply map_eq_name_eq_eq in H1.
  rewrite -H1.
  have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H4.
  case: pks2 H_eq_pks H_eq_pks2 => //= p' pks2 H_eq_pks H_eq_pks2.
  inversion H_eq_pks2.
  rewrite -H_eq_pks1.
  exists {| nwPackets := pks1 ++ pks2 ; nwState := nwState mnet |}.
  split; first exact: (@SF_drop _ _ _ _ _ _ p' pks1 pks2).
  by rewrite /tot_map_net /= map_app.
- case: mout H2 => // H_eq_mout {H_eq_mout}.
  apply map_eq_name_eq_eq in H1.
  rewrite -H1.
  have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H4.
  case: pks2 H_eq_pks H_eq_pks2 => //= p' pks2 H_eq_pks H_eq_pks2.
  inversion H_eq_pks2.
  rewrite -H_eq_pks1.
  exists {| nwPackets := p' :: pks1 ++ p' :: pks2 ; nwState := nwState mnet |}.
  split; first exact: (@SF_dup _ _ _ _ _ _ p' pks1 pks2).
  by rewrite /tot_map_net /= map_app.
- case: mout H2 => // H_eq_mout {H_eq_mout}.
  case: mfailed' H => //= h' mfailed' H_eq.
  inversion H_eq.
  apply map_eq_name_eq_eq in H1.
  rewrite -H1.
  exists mnet.
  split => //.
  exact: SF_fail.
- case: mout H4 => // H_eq_mout {H_eq_mout}.
  have H_in := H3.
  apply in_split in H_in.
  move: H_in => [ns1 [ns2 H_eq]].
  have [mns1 [mns2 [H_eq_mns [H_eq_mns1 H_eq_mns2]]]] := map_eq_inv _ _ _ _ H_eq.
  case: mns2 H_eq_mns H_eq_mns2 => //= h' mns2 H_eq_mns H_eq_mns2.
  exists {| nwPackets := nwPackets mnet ; 
       nwState := (fun nm => match name_eq_dec nm h' with
                           | left _ => (reboot (nwState mnet nm)) 
                           | right _ => (nwState mnet nm) 
                           end) |}.
  split.
  * apply (@SF_reboot _ _ _ h') => //.
    + rewrite H_eq_mns.
      apply in_or_app.
      by right; left.
    + inversion H_eq_mns2.
      rewrite -H0 in H5.
      move {H3 ns1 ns2 H_eq mns1 H_eq_mns1 h mns2 H_eq_mns H_eq_mns2 H0 H1}.
      have H_eq: remove name_eq_dec (tot_map_name h') (map tot_map_name mfailed) = map tot_map_name (remove name_eq_dec h' mfailed).
        move {H5 mfailed'}.
        elim: mfailed => //=.
        move => n l IH.
        case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' => //.
        + by apply tot_map_name_injective in H_dec.
        + by rewrite H_dec' in H_dec.
        + by rewrite /= IH.               
      rewrite H_eq in H5.
      by apply map_eq_name_eq_eq in H5.
  * rewrite /tot_map_net /=.
    inversion H_eq_mns2.
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 {nwS1 nwS2}.
      apply functional_extensionality => n.
      case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' => //.
      + rewrite -H_dec in H_dec'.
        by rewrite tot_map_name_inverse_inv in H_dec'.
      + rewrite H_dec' in H_dec.
        by rewrite tot_map_name_inv_inverse in H_dec.
    by rewrite H_eq_sw.
Qed.

End TotMapSimulations.
