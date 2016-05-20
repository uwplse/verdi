Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.

Require Import TotalMapSimulations.

Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class MultiParamsPartialExtendedMap
 (B0 : BaseParams) (B1 : BaseParams) 
 (P0 : MultiParams B0) (P1 : MultiParams B1) :=
{
  pt_ext_map_data : @data B0 -> @name _ P0 -> @data B1 ;
  pt_ext_map_input : @input B0 -> @name _ P0 -> @data B0 -> option (@input B1) ;
  pt_ext_map_msg : @msg _ P0 -> option (@msg _ P1) ;
}.

Section PartialExtendedMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {multi_map : MultiParamsPartialExtendedMap multi_fst multi_snd}.

Definition pt_ext_map_name_msgs :=
  fold_right (fun nm l => 
                match pt_ext_map_msg (snd nm) with
                | Some m => (tot_map_name (fst nm), m) :: l
                | None => l
                end) [].

Definition pt_ext_mapped_net_handlers me src m st :=
  let '(_, st', ps) := net_handlers me src m st in
  (pt_ext_map_data st' me, pt_ext_map_name_msgs ps).

Definition pt_ext_mapped_input_handlers me inp st :=
  let '(_, st', ps) := input_handlers me inp st in
  (pt_ext_map_data st' me, pt_ext_map_name_msgs ps).

End PartialExtendedMapDefs.

Class MultiParamsPartialExtendedMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (N : MultiParamsNameTotalMap P0 P1)
  (P : MultiParamsPartialExtendedMap P0 P1) :=
  {
    pt_ext_init_handlers_eq : forall n,
      pt_ext_map_data (init_handlers n) n = init_handlers (tot_map_name n) ;
    pt_ext_net_handlers_some : forall me src m st m' out st' ps,
      pt_ext_map_msg m = Some m' ->
      net_handlers (tot_map_name me) (tot_map_name src) m' (pt_ext_map_data st me) = (out, st', ps) ->
      pt_ext_mapped_net_handlers me src m st = (st', ps) ;
    pt_ext_net_handlers_none : forall me src m st out st' ps,
      pt_ext_map_msg m = None ->
      net_handlers me src m st = (out, st', ps) ->
      pt_ext_map_data st' me = pt_ext_map_data st me /\ pt_ext_map_name_msgs ps = [] ;
    pt_ext_input_handlers_some : forall me inp st inp' out st' ps,
      pt_ext_map_input inp me st = Some inp' ->
      input_handlers (tot_map_name me) inp' (pt_ext_map_data st me) = (out, st', ps) ->
      pt_ext_mapped_input_handlers me inp st = (st', ps) ;
    pt_ext_input_handlers_none : forall me inp st out st' ps,
      pt_ext_map_input inp me st = None ->
      input_handlers me inp st = (out, st', ps) ->
      pt_ext_map_data st' me = pt_ext_map_data st me /\ pt_ext_map_name_msgs ps = []
  }.

Section PartialExtendedMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {multi_map : MultiParamsPartialExtendedMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialExtendedMapCongruency name_map multi_map}.

Lemma pt_ext_init_handlers_fun_eq : 
  init_handlers = fun n : name => pt_ext_map_data (init_handlers (tot_map_name_inv n)) (tot_map_name_inv n).
Proof.
apply functional_extensionality => n.
have H_eq := pt_ext_init_handlers_eq.
rewrite H_eq {H_eq}.
by rewrite tot_map_name_inverse_inv.
Qed.

Definition pt_ext_map_packet (p : @packet _ multi_fst)  :=
match p with
| mkPacket src dst m =>
  match pt_ext_map_msg m with
  | Some m' => Some (mkPacket (tot_map_name src) (tot_map_name dst) m')
  | None => None
  end
end.

Definition pt_ext_map_packets :=
fold_right (fun p l =>
            match pt_ext_map_packet p with
            | Some p' => p' :: l
            | None => l
            end) [].

Lemma pt_ext_map_packets_app_distr : 
  forall l l',
  pt_ext_map_packets (l ++ l') = pt_ext_map_packets l ++ pt_ext_map_packets l'.
Proof.
elim => //=.
move => n l IH l'.
rewrite /= IH.
by case pt_ext_map_packet.
Qed.

Definition pt_ext_map_net (net : @network  _ multi_fst) : @network _ multi_snd :=
  {| nwPackets := pt_ext_map_packets net.(nwPackets) ;
     nwState := fun n => pt_ext_map_data (net.(nwState) (tot_map_name_inv n)) (tot_map_name_inv n) |}.

Lemma pt_ext_map_name_msgs_app_distr : 
  forall l l',
  pt_ext_map_name_msgs (l ++ l') = pt_ext_map_name_msgs l ++ pt_ext_map_name_msgs l'.
Proof.
elim => //=.
case => n m l IH l'.
rewrite /= IH.
by case (pt_ext_map_msg _) => [m'|].
Qed.

Lemma pt_ext_map_packet_map_eq :
  forall l h,
    pt_ext_map_packets (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (pt_ext_map_name_msgs l).
Proof.
move => l h.
elim: l => //=.
case => n m l IH.
case (pt_ext_map_msg _) => [m'|] //.
by rewrite IH.
Qed.

Lemma pt_ext_map_packet_eq_some :
  forall l p p',
    pt_ext_map_packet p = Some p' ->
    pt_ext_map_packets (map (fun m : name * msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := pDst p'; pDst := fst m; pBody := snd m |}) (pt_ext_map_name_msgs l).
Proof.
move => l; case => /= src dst m p.
case H_m: (pt_ext_map_msg m) => [m'|] // H_eq.
injection H_eq => H_eq_p.
rewrite -H_eq_p /=.
exact: pt_ext_map_packet_map_eq.
Qed.

Lemma pt_ext_map_update_eq :
forall f h d,
  (fun n : name => pt_ext_map_data (update f h d (tot_map_name_inv n)) (tot_map_name_inv n)) =
  update (fun n : name => pt_ext_map_data (f (tot_map_name_inv n)) (tot_map_name_inv n)) (tot_map_name h) (pt_ext_map_data d h).
Proof.
move => f h d.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' //.
- rewrite -H_dec in H_dec'.
  by rewrite H_dec.
- case: H_dec'.
  rewrite -H_dec.
  by rewrite tot_map_name_inverse_inv.
- rewrite H_dec' in H_dec.
  by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Lemma pt_ext_map_update_eq_some :
  forall net d p p',
    pt_ext_map_packet p = Some p' ->
    (fun n : name => pt_ext_map_data (update (nwState net) (pDst p) d (tot_map_name_inv n)) (tot_map_name_inv n)) =
    update (fun n : name => pt_ext_map_data (nwState net (tot_map_name_inv n)) (tot_map_name_inv n)) (pDst p') (pt_ext_map_data d (pDst p)).
Proof.
move => net d p p'.
case: p => src dst m.
case: p' => src' dst' m' /=.
case H_eq: (pt_ext_map_msg _) => [m0|] // H_eq'.
inversion H_eq'; subst.
move {H_eq H_eq'}.
exact: pt_ext_map_update_eq.
Qed.

Lemma pt_ext_map_name_msgs_empty_eq :
  forall l dst,
  pt_ext_map_name_msgs l = [] ->
  pt_ext_map_packets (map (fun m0 : name * msg => {| pSrc := dst; pDst := fst m0; pBody := snd m0 |}) l) = [].
Proof.
elim => //=.
case => n m l IH dst.
case H_m: (pt_ext_map_msg _) => [m'|] //=.
move => H_eq.
by rewrite IH.
Qed.

Theorem step_m_pt_ext_mapped_simulation_1 :
  forall net net' tr,
    @step_m _ multi_fst net net' tr ->
    (exists tr, @step_m _ multi_snd (pt_ext_map_net net) (pt_ext_map_net net') tr) \/ pt_ext_map_net net' = pt_ext_map_net net.
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  case H_m: (pt_ext_map_packet p) => [p'|].
    left.
    rewrite H_eq' /= /pt_ext_map_net /=.
    have H_eq_dst: tot_map_name (pDst p) = pDst p'.
      case: p H_eq H_hnd H_eq' H_m => /= src dst m H_eq H_hnd H_eq'.
      case (pt_ext_map_msg m) => //= m' H_m.
      by inversion H_m.
    case H_n: (net_handlers (pDst p') (pSrc p') (pBody p') (pt_ext_map_data (nwState net (pDst p)) (pDst p))) => [[out' d'] ps].
    exists [(pDst p', inr out')].
    apply SM_deliver with (xs := pt_ext_map_packets ms) (ys := pt_ext_map_packets ms') (d0 := pt_ext_map_data d (pDst p)) (l0 := pt_ext_map_name_msgs l).
    * rewrite /= H_eq pt_ext_map_packets_app_distr /=.
      case H_p: (pt_ext_map_packet _) => [p0|]; last by rewrite H_p in H_m.
      by rewrite H_p in H_m; injection H_m => H_eq_p; rewrite H_eq_p.
    * rewrite /=.
      rewrite -{2}H_eq_dst tot_map_name_inv_inverse.
      case: p H_eq H_hnd H_eq' H_m H_eq_dst H_n => /= src dst mg H_eq H_hnd H_eq'.
      case H_m: (pt_ext_map_msg mg) => [mg'|] //.
      case: p' H_eq' => src' dst' m0 H_eq' H_eq_p.
      inversion H_eq_p; subst.
      move => H_eq_dst H_eq_n {H_eq_p H_eq_dst}.
      simpl in *.
      have H_q := @pt_ext_net_handlers_some _ _ _ _ _ _ multi_map_congr dst src mg (nwState net dst) _ _ _ _ H_m H_eq_n.
      rewrite /pt_ext_mapped_net_handlers in H_q.
      rewrite H_hnd in H_q.
      find_inversion.
      by rewrite tot_map_name_inv_inverse.
    * rewrite /= /pt_ext_map_net /= 2!pt_ext_map_packets_app_distr.
      rewrite (pt_ext_map_packet_eq_some _ _ H_m).
      by rewrite (pt_ext_map_update_eq_some _ _ _ H_m).
  right.
  rewrite H_eq' /= {H_eq'}.
  rewrite /pt_ext_map_net /=.
  case: p H_eq H_hnd H_m => /= src dst m H_eq H_hnd.
  case H_m: (pt_ext_map_msg _) => [m'|] // H_eq' {H_eq'}.
  rewrite 2!pt_ext_map_packets_app_distr H_eq pt_ext_map_packets_app_distr /=.
  case H_m': (pt_ext_map_msg _) => [m'|]; first by rewrite H_m' in H_m.
  have [H_d H_l] := pt_ext_net_handlers_none _ _ _ _ H_m H_hnd.
  rewrite (pt_ext_map_name_msgs_empty_eq _ dst H_l) /=.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
      case name_eq_dec => H_dec //.
      by rewrite H_dec H_d.
    by rewrite H_eq_s.
- move => h net net' out inp d l H_hnd H_eq.  
  case H_i: (pt_ext_map_input inp h (nwState net h)) => [inp'|].
    left.
    case H_h: (input_handlers (tot_map_name h) inp' (pt_ext_map_data (nwState net h) h)) => [[out' d'] ps].
    exists [(tot_map_name h, inl inp'); (tot_map_name h, inr out')].
    apply (@SM_input _ _ _ _ _ _ _ (pt_ext_map_data d h) (pt_ext_map_name_msgs l)).
      rewrite /=.
      have H_q := @pt_ext_input_handlers_some _ _ _ _ _ _ multi_map_congr h inp (nwState net h) _ _ _ _ H_i H_h.
      rewrite /pt_ext_mapped_input_handlers /= in H_q.
      rewrite H_hnd in H_q.
      find_inversion.
      by rewrite tot_map_name_inv_inverse.
    rewrite /= H_eq /= /pt_ext_map_net /= pt_ext_map_packets_app_distr pt_ext_map_packet_map_eq.
    by rewrite -pt_ext_map_update_eq.
  right.
  rewrite H_eq /pt_ext_map_net /=.
  have [H_d H_l] := pt_ext_input_handlers_none _ _ _ H_i H_hnd.
  rewrite pt_ext_map_packets_app_distr.
  rewrite (pt_ext_map_name_msgs_empty_eq _ h H_l) /=.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 /=.
      apply functional_extensionality => n.
      rewrite /update /=.
      case name_eq_dec => H_dec //.
      by rewrite H_dec H_d.
    by rewrite H_eq_s.
Qed.

Corollary step_m_pt_ext_mapped_simulation_star_1 :
  forall net tr,
    @step_m_star _ multi_fst step_m_init net tr ->
    exists tr', @step_m_star _ multi_snd step_m_init (pt_ext_map_net net) tr'.
Proof.
move => net tr H_step.
remember step_m_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_m_init /= /pt_ext_map_net /=.
  rewrite pt_ext_init_handlers_fun_eq.
  exists [].  
  exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_m_pt_ext_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' H_star].
  move: H => [tr'' H].
  exists (tr' ++ tr'').
  have H_trans := refl_trans_1n_trace_trans H_star.
  apply: H_trans.
  have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
  apply: (@RT1nTStep _ _ _ _ (pt_ext_map_net x'')) => //.
  exact: RT1nTBase.
move: H => [H_eq H_eq'].
move: IHH_step1 => [tr' H_star].
exists tr'.
rewrite /pt_ext_map_net.
by rewrite H_eq H_eq'.
Qed.

End PartialExtendedMapSimulations.
