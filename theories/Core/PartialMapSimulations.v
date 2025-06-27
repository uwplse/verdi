From Verdi Require Import Verdi DynamicNetLemmas TotalMapSimulations.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Sumbool Sorting.Permutation.
From Verdi Require Import DynamicNetLemmas.
From Verdi Require Import Ssrexport.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Class BaseParamsPartialMap (P0 : BaseParams) (P1 : BaseParams) := 
  {
    pt_map_data : @data P0 -> @data P1 ;
    pt_map_input : @input P0 -> option (@input P1) ;
    pt_map_output : @output P0 -> option (@output P1)
  }.

Class MultiParamsMsgPartialMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : MultiParams B1) :=
  {
    pt_map_msg : @msg B0 P0 -> option (@msg B1 P1)
  }.

Section PartialMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.

Definition pt_map_name_msg nm :=
  match pt_map_msg (snd nm) with
  | Some m => Some (tot_map_name (fst nm), m)
  | None => None
  end.

Definition pt_mapped_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (filterMap pt_map_output out, pt_map_data st', filterMap pt_map_name_msg ps).

Definition pt_mapped_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (filterMap pt_map_output out, pt_map_data st', filterMap pt_map_name_msg ps).

End PartialMapDefs.

Class MultiParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (B : BaseParamsPartialMap B0 B1) 
  (N : MultiParamsNameTotalMap P0 P1)
  (P : MultiParamsMsgPartialMap P0 P1) : Prop :=
  {
    pt_init_handlers_eq : forall n, 
      pt_map_data (init_handlers n) = init_handlers (tot_map_name n) ;
    pt_net_handlers_some : forall me src m st m',
      pt_map_msg m = Some m' ->
      pt_mapped_net_handlers me src m st = 
        net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) ;
    pt_net_handlers_none : forall me src m st out st' ps,
      pt_map_msg m = None ->
      net_handlers me src m st = (out, st', ps) ->
      pt_map_data st' = pt_map_data st /\ 
        filterMap pt_map_name_msg ps = [] /\ filterMap pt_map_output out = [] ;
    pt_input_handlers_some : forall me inp st inp',
      pt_map_input inp = Some inp' ->
      pt_mapped_input_handlers me inp st = 
        input_handlers (tot_map_name me) inp' (pt_map_data st) ;
    pt_input_handlers_none : forall me inp st out st' ps,
      pt_map_input inp = None ->
      input_handlers me inp st = (out, st', ps) ->
      pt_map_data st' = pt_map_data st /\ 
        filterMap pt_map_name_msg ps = [] /\ filterMap pt_map_output out = []
  }.

Class FailureParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailureParams P0) (F1 : FailureParams P1)
  (B : BaseParamsPartialMap B0 B1) : Prop :=
  {
    pt_reboot_eq : forall d, pt_map_data (reboot d) = reboot (pt_map_data d)
  }.

Class FailMsgParamsPartialMapCongruency 
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailMsgParams P0) (F1 : FailMsgParams P1)
  (P : MultiParamsMsgPartialMap P0 P1) : Prop :=
  {
    pt_fail_msg_fst_snd : pt_map_msg msg_fail = Some msg_fail
  }.

Class NewMsgParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (N0 : NewMsgParams P0) (N1 : NewMsgParams P1)
  (P : MultiParamsMsgPartialMap P0 P1) : Prop :=
  {
    pt_new_msg_fst_snd : pt_map_msg msg_new = Some msg_new
  }.

Section PartialMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map msg_map}.

Definition pt_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) :
 option (@name _ multi_snd * (@input base_snd + list (@output base_snd))) :=
match e with
| (n, inl io) => 
  match pt_map_input io with
  | Some io' => Some (tot_map_name n, inl io')
  | None => None
  end
| (n, inr out) => Some (tot_map_name n, inr (filterMap pt_map_output out))
end.

Definition pt_map_packet (p : @packet _ multi_fst)  :=
match p with
| mkPacket src dst m =>
  match pt_map_msg m with
  | Some m' => Some (mkPacket (tot_map_name src) (tot_map_name dst) m')
  | None => None
  end
end.

Definition pt_map_net (net : @network _ multi_fst) : @network _ multi_snd :=
  {| nwPackets := filterMap pt_map_packet net.(nwPackets) ;
     nwState := fun n => pt_map_data (net.(nwState) (tot_map_name_inv n)) |}.

Lemma pt_init_handlers_fun_eq : 
    init_handlers = fun n : name => pt_map_data (init_handlers (tot_map_name_inv n)).
Proof using name_map_bijective multi_map_congr msg_map.
apply functional_extensionality => n.
have H_eq := pt_init_handlers_eq.
rewrite H_eq {H_eq}.
by rewrite tot_map_name_inverse_inv.
Qed.

Lemma filterMap_pt_map_name_msg_empty_eq :
  forall l dst,
  filterMap pt_map_name_msg l = [] ->
  filterMap pt_map_packet (map (fun m0 : name * msg => {| pSrc := dst; pDst := fst m0; pBody := snd m0 |}) l) = [].
Proof using.
elim => //=.
case => /= n m l IH dst.
rewrite /pt_map_name_msg /=.
case pt_map_msg => [m'|] H_eq //=.
by rewrite IH.
Qed.

Lemma filterMap_pt_map_packet_map_eq :
  forall l h,
    filterMap pt_map_packet (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (filterMap pt_map_name_msg l).
Proof using.
move => l h.
elim: l => //=.
case => n m l IH.
rewrite /pt_map_name_msg /=.
case pt_map_msg => [m'|] //.
by rewrite IH.
Qed.

Lemma filterMap_pt_map_packet_map_eq_some :
  forall l p p',
    pt_map_packet p = Some p' ->
    filterMap pt_map_packet (map (fun m : name * msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := pDst p'; pDst := fst m; pBody := snd m |}) (filterMap pt_map_name_msg l).
Proof using.
move => l; case => /= src dst m p.
case H_m: (pt_map_msg m) => [m'|] // H_eq.
injection H_eq => H_eq_p.
rewrite -H_eq_p /=.
exact: filterMap_pt_map_packet_map_eq.
Qed.

Lemma pt_map_update_eq :
forall f h d,
  (fun n : name => pt_map_data (update name_eq_dec f h d (tot_map_name_inv n))) =
  update name_eq_dec (fun n : name => pt_map_data (f (tot_map_name_inv n))) (tot_map_name h) (pt_map_data d).
Proof using name_map_bijective.
move => f h d.
apply functional_extensionality => n.
rewrite /update /=.
case: name_eq_dec => H_dec; case name_eq_dec => H_dec' //.
  rewrite -H_dec in H_dec'.
  by rewrite tot_map_name_inverse_inv in H_dec'.
rewrite H_dec' in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Lemma pt_map_update_eq_some :
  forall net d p p',
    pt_map_packet p = Some p' ->
    (fun n : name => pt_map_data (update name_eq_dec (nwState net) (pDst p) d (tot_map_name_inv n))) =
    update name_eq_dec (fun n : name => pt_map_data (nwState net (tot_map_name_inv n))) (pDst p') (pt_map_data d).
Proof using name_map_bijective.
move => net d p p'.
case: p => src dst m.
case: p' => src' dst' m' /=.
case H_eq: (pt_map_msg _) => [m0|] // H_eq'.
inversion H_eq'; subst.
move {H_eq H_eq'}.
exact: pt_map_update_eq.
Qed.

Theorem step_async_pt_mapped_simulation_1 :
  forall net net' tr,
    @step_async _ multi_fst net net' tr ->
    @step_async _ multi_snd (pt_map_net net) (pt_map_net net') (filterMap pt_map_trace_occ tr) \/ 
    (pt_map_net net' = pt_map_net net /\ filterMap trace_non_empty_out (filterMap pt_map_trace_occ tr) = []).
Proof using name_map_bijective multi_map_congr.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  rewrite /=.  
  case H_m: (pt_map_packet p) => [p'|].
    have ->: tot_map_name (pDst p) = pDst p'.
      case: p H_eq H_hnd H_eq' H_m => /= src dst m H_eq H_hnd H_eq'.
      case (pt_map_msg m) => //= m' H_m.
      by inversion H_m.
    left.
    rewrite H_eq' /=.
    apply (@StepAsync_deliver _ _ _ _ _ (filterMap pt_map_packet ms) (filterMap pt_map_packet ms') (filterMap pt_map_output out) (pt_map_data d) (filterMap pt_map_name_msg l)).
    * rewrite /= H_eq filterMap_app /=.
      case H_p: (pt_map_packet _) => [p0|].
        rewrite H_p in H_m.
        by injection H_m => H_eq_p; rewrite H_eq_p.
      by rewrite H_p in H_m.
    * rewrite /=.
      case: p H_eq H_hnd H_eq' H_m => /= src dst m H_eq H_hnd H_eq'.
      case H_m: (pt_map_msg m) => [m'|] //.
      case: p' H_eq' => src' dst' m0 H_eq' H_eq_p.
      inversion H_eq_p; subst.
      rewrite /= {H_eq_p}.
      have H_q := pt_net_handlers_some dst src m (nwState net dst) H_m.
      rewrite /pt_mapped_net_handlers in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * rewrite /= /pt_map_net /= 2!filterMap_app.
      by rewrite (filterMap_pt_map_packet_map_eq_some _ _ H_m) (pt_map_update_eq_some _ _ _ H_m).
  right.
  split.
  * rewrite H_eq' {H_eq'}.
    rewrite /pt_map_net /=.
    case: p H_eq H_hnd H_m => /= src dst m H_eq H_hnd.
    case H_m: (pt_map_msg _) => [m'|] // H_eq'.
    rewrite 2!filterMap_app H_eq filterMap_app /=.
    case H_m': (pt_map_msg _) => [m'|]; first by rewrite H_m' in H_m.
    have [H_d [H_l H_o]] := pt_net_handlers_none _ _ _ _ H_m H_hnd.
    rewrite (filterMap_pt_map_name_msg_empty_eq _ dst H_l) /=.
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_s: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 /=.
      apply functional_extensionality => n.
      rewrite /update /=.
      case: (name_eq_dec _ _) => H_dec //.
      by rewrite H_dec H_d.
    by rewrite H_eq_s.
  * move {H_eq'}.
    case: p H_eq H_hnd H_m => /= src dst m H_eq H_hnd.
    case H_m: (pt_map_msg _) => [m'|] // H_eq'.
    have [H_d [H_l H_o]] := pt_net_handlers_none _ _ _ _ H_m H_hnd.
    by rewrite H_o.
- move => h net net' out inp d l H_hnd H_eq.
  rewrite /=.
  case H_i: (pt_map_input inp) => [inp'|].
    left.
    apply (@StepAsync_input _ _ _ _ _ _ _ (pt_map_data d) (filterMap pt_map_name_msg l)).
      rewrite /=.
      have H_q := pt_input_handlers_some h inp (nwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    rewrite /= H_eq /= /pt_map_net /=.
    rewrite -filterMap_pt_map_packet_map_eq filterMap_app.
    by rewrite -pt_map_update_eq.
  right.
  split.
  * rewrite H_eq /pt_map_net /=.
    have [H_d [H_l H_o]] := pt_input_handlers_none _ _ _ H_i H_hnd.
    rewrite filterMap_app.
    rewrite (filterMap_pt_map_name_msg_empty_eq _ h H_l) /=.
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_s: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 /=.
      apply functional_extensionality => n.
      rewrite /update /=.
      case: (name_eq_dec _ _) => H_dec //.
      by rewrite H_dec H_d.
    by rewrite H_eq_s.
  * rewrite /=.
    have [H_d [H_l H_o]] := pt_input_handlers_none _ _ _ H_i H_hnd.
    by rewrite H_o.
Qed.

Corollary step_async_pt_mapped_simulation_star_1 :
  forall net tr,
    @step_async_star _ multi_fst step_async_init net tr ->
    exists tr', @step_async_star _ multi_snd step_async_init (pt_map_net net) tr' /\ 
     filterMap trace_non_empty_out (filterMap pt_map_trace_occ tr) = filterMap trace_non_empty_out tr'.
Proof using name_map_bijective multi_map_congr.
move => net tr H_step.
remember step_async_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_async_init /= /pt_map_net /=.
  rewrite pt_init_handlers_fun_eq.
  exists [].
  split => //.
  exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_async_pt_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' [H_star H_eq_tr]].
  exists (tr' ++ filterMap pt_map_trace_occ tr2).
  split.
  * have H_trans := refl_trans_1n_trace_trans H_star.
    apply: H_trans.
    rewrite -(app_nil_r (filterMap pt_map_trace_occ _)).
    apply: (@RT1nTStep _ _ _ _ (pt_map_net x'')) => //.
    exact: RT1nTBase.
  * by rewrite 2!filterMap_app H_eq_tr filterMap_app.
move: H => [H_eq H_eq'].
rewrite H_eq.
move: IHH_step1 => [tr' [H_star H_tr]].
exists tr'.
split => //.
rewrite 2!filterMap_app.
by rewrite H_eq' app_nil_r.
Qed.

Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.
Context {fail_map_congr : FailureParamsPartialMapCongruency fail_fst fail_snd base_map}.

Theorem step_failure_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_failure _ _ fail_fst (failed, net) (failed', net') tr ->
    @step_failure _ _ fail_snd (map tot_map_name failed, pt_map_net net) (map tot_map_name failed', pt_map_net net') (filterMap pt_map_trace_occ tr) \/ 
    (pt_map_net net' = pt_map_net net /\ failed = failed' /\ filterMap trace_non_empty_out (filterMap pt_map_trace_occ tr) = []).
Proof using name_map_bijective multi_map_congr fail_map_congr.
move => net net' failed failed' tr H_step.
invcs H_step.
- rewrite /=.
  case H_m: (pt_map_packet p) => [p'|].
    destruct p, p'.
    simpl in *.
    move: H_m.
    case H_m: pt_map_msg => [m|] //.
    move => H_eq.
    find_inversion.
    left.
    rewrite /pt_map_net /= H3 filterMap_app /= H_m /= 2!filterMap_app {H3}.
    set p' := {| pSrc := _ ; pDst := _ ; pBody := _ |}.
    have ->: tot_map_name pDst = Net.pDst p' by [].    
    apply (@StepFailure_deliver _ _ _ _ _ _ _ (filterMap pt_map_packet xs) (filterMap pt_map_packet ys) (filterMap pt_map_output out) (pt_map_data d) (filterMap pt_map_name_msg l)) => //=.
    * exact: not_in_failed_not_in.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ H_m)  /pt_mapped_net_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by find_inversion.
    * pose p := {| pSrc := pSrc ; pDst := pDst ; pBody := pBody |}.
      have H_p: pt_map_packet p = Some p'.
        rewrite /pt_map_packet.
        break_match.
        rewrite /p in Heqp0.
        find_inversion.
        by rewrite H_m.      
      by rewrite (filterMap_pt_map_packet_map_eq_some _ _ H_p) (pt_map_update_eq_some _ _ _ H_p).
  right.
  rewrite /pt_map_net /=.
  destruct p.
  simpl in *.
  move: H_m.
  case H_m: pt_map_msg => [m|] //.
  move => H_eq.
  have H_m' := @pt_net_handlers_none _ _ _ _ _ name_map msg_map multi_map_congr _ _ _ _ _ _ _ H_m H6.
  break_and.
  rewrite H3 3!filterMap_app H1.    
  rewrite (filterMap_pt_map_name_msg_empty_eq _ pDst H0) /= H_m.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case: (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec.
  by rewrite H_eq_s.
- rewrite /= /pt_map_net /=.
  case H_i: pt_map_input => [inp'|].
    left.
    apply (@StepFailure_input _ _ _ _ _ _ _ _ _ (pt_map_data d) (filterMap pt_map_name_msg l)).
    * exact: not_in_failed_not_in.
    * rewrite /= -(pt_input_handlers_some _ _ _ H_i)  /pt_mapped_input_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by tuple_inversion.
    * rewrite /= -filterMap_pt_map_packet_map_eq -filterMap_app.
      by rewrite pt_map_update_eq.
  right.
  rewrite /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none _ _ _ H_i H5.
  rewrite H_o.
  split => //.
  rewrite filterMap_app.
  rewrite (filterMap_pt_map_name_msg_empty_eq _ h H_l) /=.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case: (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec H_d.
  by rewrite H_eq_s.
- case H_m: (pt_map_packet p) => [p'|].
    left.
    destruct p, p'.
    simpl in *.
    move: H_m.
    case H_m: pt_map_msg => [m|] //.
    move => H_eq.
    find_inversion.
    rewrite /pt_map_net /=.
    find_rewrite.
    rewrite filterMap_app /= H_m filterMap_app.
    move: H4.
    set p := {| pSrc := _ ; pDst := _ ; pBody := _ |}.
    move => H_eq.
    set p' := {| pSrc := _ ; pDst := _ ; pBody := _ |}.
    exact: (@StepFailure_drop _ _ _ _ _ _ p' (filterMap pt_map_packet xs) (filterMap pt_map_packet ys)).
  right.
  split => //.
  rewrite /pt_map_net /=.
  find_rewrite.
  by rewrite 2!filterMap_app /= H_m.
- rewrite /pt_map_net /=.
  find_rewrite.
  case H_p: pt_map_packet => [p'|]; last by right.
  left.
  rewrite filterMap_app /= H_p.
  exact: (@StepFailure_dup _ _ _ _ _ _ p' (filterMap pt_map_packet xs) (filterMap pt_map_packet ys)).
- left.
  exact: StepFailure_fail.
- rewrite remove_tot_map_eq /=.
  left.
  rewrite {2}/pt_map_net /=.
  eapply (@StepFailure_reboot _ _ _ (tot_map_name h)) => //; first exact: in_failed_in.
  by rewrite pt_map_update_eq /pt_map_net pt_reboot_eq /= tot_map_name_inv_inverse.
Qed.

Corollary step_failure_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_failure_star _ _ fail_fst step_failure_init (failed, net) tr ->
    exists tr', @step_failure_star _ _ fail_snd step_failure_init (map tot_map_name failed, pt_map_net net) tr' /\ 
     filterMap trace_non_empty_out (filterMap pt_map_trace_occ tr) = filterMap trace_non_empty_out tr'.
Proof using name_map_bijective multi_map_congr fail_map_congr.
move => net failed tr H_step.
remember step_failure_init as y in *.
have H_eq_f: failed = fst (failed, net) by [].
have H_eq_n: net = snd (failed, net) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_n {H_eq_n}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_failure_init /= /pt_map_net /=.
  rewrite -pt_init_handlers_fun_eq.
  exists [].
  split => //.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_failure_pt_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' [H_star H_eq_tr]].
  exists (tr' ++ filterMap pt_map_trace_occ tr2).
  split.
  * have H_trans := refl_trans_1n_trace_trans H_star.
    apply: H_trans.
    rewrite -(app_nil_r (filterMap pt_map_trace_occ _)).
    apply: (@RT1nTStep _ _ _ _ (map tot_map_name failed'', pt_map_net net'')) => //.
    exact: RT1nTBase.
  * by rewrite 3!filterMap_app H_eq_tr.
move: H => [H_eq_n [H_eq_f H_eq]].
rewrite H_eq_n -H_eq_f.
move: IHH_step1 => [tr' [H_star H_tr]].
exists tr'.
split => //.
rewrite 2!filterMap_app.
by rewrite H_eq app_nil_r.
Qed.

Definition pt_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd :=
  {| onwPackets := fun src dst => filterMap pt_map_msg (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     onwState := fun n => pt_map_data (onet.(onwState) (tot_map_name_inv n)) |}.

Lemma pt_map_msg_update2 : 
  forall f ms to from,
    (fun src dst => filterMap pt_map_msg (update2 name_eq_dec f from to ms (tot_map_name_inv src) (tot_map_name_inv dst))) =
    update2 name_eq_dec (fun src0 dst0 : name => filterMap pt_map_msg (f (tot_map_name_inv src0) (tot_map_name_inv dst0)))
        (tot_map_name from) (tot_map_name to) (filterMap pt_map_msg ms).
Proof using name_map_bijective.
move => f ms to from.
apply functional_extensionality => src.
apply functional_extensionality => dst.
rewrite /update2 /=.
case sumbool_and => H_dec; case sumbool_and => H_dec' //.
  move: H_dec => [H_eq H_eq'].
  case: H_dec' => H_dec'.
    rewrite H_eq in H_dec'.
    by rewrite tot_map_name_inverse_inv in H_dec'.
  rewrite H_eq' in H_dec'.
  by rewrite tot_map_name_inverse_inv in H_dec'.
move: H_dec' => [H_eq H_eq'].
case: H_dec => H_dec.
  rewrite -H_eq in H_dec.
  by rewrite tot_map_name_inv_inverse in H_dec.
rewrite -H_eq' in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Lemma collate_pt_map_eq :
  forall f h l,
    (fun src dst => filterMap pt_map_msg (collate name_eq_dec h f l (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate name_eq_dec (tot_map_name h) (fun src dst => filterMap pt_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (filterMap pt_map_name_msg l).
Proof using name_map_bijective.
move => f h l.
elim: l h f => //.
case => n m l IH h f.
rewrite /= IH /= /pt_map_name_msg /=.
case H_m: pt_map_msg => [m'|] /=.
  rewrite 2!tot_map_name_inv_inverse /=.
  set f1 := fun _ _ => _.
  set f2 := update2 _ _ _ _ _.
  have H_eq_f: f1 = f2.
    rewrite /f1 /f2 {f1 f2}.
    have H_eq := pt_map_msg_update2 f (f h n ++ [m]) n h.
    move: H_eq.
    rewrite filterMap_app /=.
    case H_m': pt_map_msg => [m0|]; last by rewrite H_m' in H_m.
    rewrite H_m' in H_m.
    by inversion H_m.
  by rewrite H_eq_f.
rewrite pt_map_msg_update2 /= filterMap_app /=.
case H_m': (pt_map_msg _) => [m'|]; first by rewrite H_m' in H_m.
rewrite app_nil_r.
set f1 := update2 _ _ _ _ _.
set f2 := fun _ _ => _ _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  apply functional_extensionality => src.
  apply functional_extensionality => dst.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec //.
  move: H_dec => [H_eq H_eq'].
  by rewrite -H_eq -H_eq' 2!tot_map_name_inv_inverse.
by rewrite H_eq_f.
Qed.

Lemma collate_pt_map_update2_eq :
  forall f from to ms l,
    (fun src dst => filterMap pt_map_msg
            (collate name_eq_dec to (update2 name_eq_dec f from to ms) l
               (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate name_eq_dec (tot_map_name to)
            (update2 name_eq_dec
               (fun src dst : name =>
                filterMap pt_map_msg
                  (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name from)
               (tot_map_name to) (filterMap pt_map_msg ms)) (filterMap pt_map_name_msg l).
Proof using name_map_bijective.
move => f from to ms l.
rewrite -pt_map_msg_update2.
by rewrite collate_pt_map_eq.
Qed.

Definition pt_map_trace_ev (e : @name _ multi_fst * (@input base_fst + (@output base_fst))) :
 option (@name _ multi_snd * (@input base_snd + (@output base_snd))) :=
match e with
|  (n, inl i) => 
  match pt_map_input i with
  | Some i' => Some (tot_map_name n, inl i')
  | None => None
  end
| (n, inr o) => 
  match pt_map_output o with
  | Some o' => Some (tot_map_name n, inr o')
  | None => None
  end
end.

Lemma filterMap_pt_map_trace_ev_outputs_eq :
  forall out to,
    filterMap pt_map_trace_ev (map2fst to (map inr out)) =
    map2fst (tot_map_name to) (map inr (filterMap pt_map_output out)).
Proof using.
elim => //=.
move => o out IH to.
by case pt_map_output => [o'|]; rewrite IH.
Qed.

Theorem step_ordered_pt_mapped_simulation_1 :
  forall net net' tr,
    @step_ordered _ multi_fst net net' tr ->
    @step_ordered _ multi_snd (pt_map_onet net) (pt_map_onet net') (filterMap pt_map_trace_ev tr) \/ 
    pt_map_onet net' = pt_map_onet net /\ filterMap pt_map_trace_ev tr = [].
Proof using name_map_bijective multi_map_congr.
move => net net' tr.
case => {net net' tr}.
- move => net net' tr m ms out d l from to H_eq H_hnd H_eq' H_eq_tr.
  destruct (pt_map_msg m) eqn:?.
    left.
    rewrite H_eq' /= /pt_map_onet /=.
    apply (@StepOrdered_deliver _ _ _ _ _ m0 (filterMap pt_map_msg ms) (filterMap pt_map_output out) (pt_map_data d) (filterMap pt_map_name_msg l) (tot_map_name from) (tot_map_name to)).
    * rewrite /= 2!tot_map_name_inv_inverse H_eq /=.
      destruct (pt_map_msg _) eqn:?; last by congruence.
      by find_injection.
    * rewrite /= tot_map_name_inv_inverse.
      rewrite -(pt_net_handlers_some _ _ _ _ Heqo).
      rewrite /pt_mapped_net_handlers /=.
      repeat break_let.
      by inversion H_hnd.
    * by rewrite /= pt_map_update_eq collate_pt_map_update2_eq.
    * by rewrite H_eq_tr /= filterMap_pt_map_trace_ev_outputs_eq.
  right.
  rewrite /=.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ Heqo H_hnd.
  rewrite H_eq_tr filterMap_pt_map_trace_ev_outputs_eq H_out /=.
  split => //.
  rewrite H_eq' /pt_map_onet /=.
  rewrite pt_map_update_eq /= H_eq_d.
  rewrite collate_pt_map_eq H_ms /=.
  set nwS1 := update _ _ _ _.
  set nwS2 := fun n => pt_map_data _.
  set nwP1 := fun _ _ => _. 
  set nwP2 := fun _ _ => _. 
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 {nwS1 nwS2}.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.  
  have H_eq_p: nwP1 = nwP2.
    rewrite /nwP1 /nwP2 /=.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move: H_dec => [H_eq_from H_eq_to].
    rewrite -H_eq_from -H_eq_to H_eq /=.
    case H_m': (pt_map_msg _) => [m'|] //.
    by rewrite H_m' in Heqo.
  by rewrite H_eq_s H_eq_p.
- move => h net net' tr out inp d l H_hnd H_eq H_eq_tr.
  destruct (pt_map_input inp) eqn:?.
    left.
    apply (@StepOrdered_input _ _ (tot_map_name h) _ _ _ (filterMap pt_map_output out) i (pt_map_data d) (filterMap pt_map_name_msg l)).
    * rewrite /=.
      have H_q := pt_input_handlers_some h inp (onwState net h) Heqo.
      rewrite /pt_mapped_input_handlers /= in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * by rewrite H_eq /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
    * by rewrite H_eq_tr /= Heqo filterMap_pt_map_trace_ev_outputs_eq.
  right.
  rewrite /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) Heqo H_hnd.
  rewrite H_eq_tr /= filterMap_pt_map_trace_ev_outputs_eq Heqo H_o /=.
  split => //.
  rewrite H_eq /= /pt_map_onet /=.
  rewrite pt_map_update_eq /= H_d.
  rewrite collate_pt_map_eq H_l /=.
  set nwS1 := update _ _ _ _.
  set nwS2 := fun n => pt_map_data _.
  have H_eq_n: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.
  by rewrite H_eq_n.
Qed.

Corollary step_ordered_pt_mapped_simulation_star_1 :
  forall net tr,
    @step_ordered_star _ multi_fst step_ordered_init net tr ->
    @step_ordered_star _ multi_snd step_ordered_init (pt_map_onet net) (filterMap pt_map_trace_ev tr).
Proof using name_map_bijective multi_map_congr.
move => net tr H_step.
remember step_ordered_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_ordered_init /= /pt_map_net /=.
  rewrite pt_init_handlers_fun_eq.
  exact: RT1nTBase.
rewrite filterMap_app.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_ordered_pt_mapped_simulation_1 in H.
case: H => H.
  have H_trans := refl_trans_1n_trace_trans IHH_step1.
  apply: H_trans.
  rewrite -(app_nil_r (filterMap pt_map_trace_ev _)).
  apply: (@RT1nTStep _ _ _ _ (pt_map_onet x'')) => //.
  exact: RT1nTBase.
move: H => [H_eq H_eq'].
by rewrite H_eq H_eq' app_nil_r.
Qed.

Lemma pt_msg_in_map :
  forall m l n m',
  (forall nm, In nm l -> snd nm = m) ->
  In (tot_map_name n, m') (filterMap pt_map_name_msg l) ->
  pt_map_msg m = Some m'.
Proof using.
move => m.
elim => //=.
case => /= n m' l IH n' m0 H_in.
rewrite /pt_map_name_msg /=.
case H_m: (pt_map_msg m') => [m1|].
  have H_in_f := H_in (n, m').
  rewrite /= in H_in_f.
  move => H_in_map.
  case: H_in_map => H_in_map.
    inversion H_in_map.    
    rewrite H_in_f in H_m; last by left.
    by rewrite -H1.
  move: H_in_map.
  apply: (IH _ m0) => //.
  move => nm H_in'.
  apply: H_in.
  by right.
apply: (IH _ m0) => //.
move => nm H_in'.
apply: H_in => //.
by right.
Qed.

Lemma pt_map_in_in :
  forall m m0 n l,
  (forall nm, In nm l -> snd nm = m) ->
  ~ In (n, m) l ->  
  ~ In (tot_map_name n, m0) (filterMap pt_map_name_msg l).
Proof using name_map_bijective.
move => m m0 n.
elim => //=.
case => /= n' m' l IH H_fail H_in.
rewrite /pt_map_name_msg /=.
case H_m: (pt_map_msg _) => [m1|].
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    have H_nm := H_fail (n', m').
    rewrite /= in H_nm.
    case: H_in.
    left.
    apply tot_map_name_injective in H0.
    rewrite H0.
    rewrite H_nm //.
    by left.
  contradict H_in'.
  apply: IH.
    move => nm H_in_nm.
    apply: H_fail.
    by right.
  move => H_in_nm.
  case: H_in.
  by right.
apply: IH.
  move => nm H_in'.
  apply: H_fail => //.
  by right.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma nodup_pt_map :
  forall m nms,
  (forall nm, In nm nms -> snd nm = m) ->
  NoDup nms ->
  NoDup (filterMap pt_map_name_msg nms).
Proof using name_map_bijective.
move => m.
elim => /=.
  move => H_m H_nd.
  exact: NoDup_nil.
case => n m0 l IH H_m H_nd.
inversion H_nd.
rewrite /=.
have H_m0 := H_m (n, m0) (or_introl (eq_refl _)).
rewrite /= in H_m0.
rewrite H_m0.
rewrite H_m0 {m0 H_m0} in H_m H_nd H1 H.
rewrite /pt_map_name_msg /=.
case H_m': (pt_map_msg _) => [m'|].
  apply NoDup_cons.
    apply: (@pt_map_in_in m) => //.
    move => nm H_in.
    by apply: H_m; right.
  apply: IH => //.
  move => nm H_in.
  by apply: H_m; right.
apply: IH => //.
move => nm H_in.
by apply: H_m; right.
Qed.

Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.

Lemma pt_map_in_snd :
   forall m m' h ns nm,
   pt_map_msg m' = Some m ->
   In nm (filterMap pt_map_name_msg (map2snd m' (filter_rel adjacent_to_dec h ns))) ->
   snd nm = m.
Proof using.
move => m m' h.
elim => //=.
move => n ns IH.
case: (adjacent_to_dec _ _) => H_dec /=; last exact: IH.
case => n' m0 H_eq.
rewrite /pt_map_name_msg /=.
case H_eq': (pt_map_msg m') => [m1|]; last by rewrite H_eq' in H_eq.
rewrite H_eq' in H_eq.
inversion H_eq.
rewrite H0 in H_eq'.
move {H_eq H0 m1}.
move => H_in.
case: H_in => H_in; first by inversion H_in.
exact: (IH (n', m0)).
Qed.

Lemma pt_in_tot_map_name :
forall m m' l n,
pt_map_msg m = Some m' ->
(forall nm, In nm l -> snd nm = m) ->
In (n, m') (filterMap pt_map_name_msg l) ->
In (tot_map_name_inv n, m) l.
Proof using name_map_bijective.
move => m m'.
elim => //=.
case => /= n m0 l IH n' H_eq H_in.
rewrite /pt_map_name_msg /=.
case H_m: (pt_map_msg _) => [m1|].
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    rewrite tot_map_name_inv_inverse.
    have H_nm := H_in (n, m0).
    rewrite -H_nm /=; first by left.
    by left.
  right.
  apply: IH => //.
  move => nm H_inn.
  apply: H_in.
  by right.
move => H_in'.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma in_pt_map_map_pair :
  forall m m' l n,
    pt_map_msg m = Some m' ->
    (forall nm, In nm l -> snd nm = m) ->
    In (tot_map_name_inv n, m) l ->
    In (n, m') (filterMap pt_map_name_msg l).
Proof using name_map_bijective.
move => m m'.
elim => //=.
case => n m0 /= l IH n' H_eq H_in.
rewrite /pt_map_name_msg /=.
case H_m: (pt_map_msg m0) => [m1|].
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    rewrite H1 in H_m.
    rewrite H_m in H_eq.
    inversion H_eq.
    left.
    by rewrite tot_map_name_inverse_inv.
  right.
  apply: IH => //.
  move => nm H_inn.
  apply: H_in.
  by right.
move => H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  rewrite H1 in H_m.
  by rewrite H_m in H_eq.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Lemma pt_nodup_perm_map_map_pair_perm :
  forall m m' h failed ns ns',
  NoDup ns ->
  Permutation (map tot_map_name ns) ns' ->
  pt_map_msg m = Some m' ->
  Permutation 
    (filterMap pt_map_name_msg (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns))))
    (map2snd m' (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) ns'))).
Proof using overlay_map_congr name_map_bijective.
move => m m' h failed ns ns' H_nd H_pm H_eq.
apply NoDup_Permutation; last split.
- apply (@nodup_pt_map m); first exact: in_map2snd_snd.
  apply NoDup_map2snd.
  exact: NoDup_remove_all.
- apply NoDup_map2snd.
  apply NoDup_remove_all.
  move: H_pm.
  apply: NoDup_Permutation_NoDup.
  exact: nodup_to_map_name.
- case: x => n m0 H_in.
  have H_eq' := pt_map_in_snd _ _ _ _ H_eq H_in.
  rewrite /= in H_eq'.
  rewrite H_eq' in H_in.
  rewrite H_eq' {H_eq' m0}.
  apply (@pt_in_tot_map_name m) in H_in => //.
    apply in_map_pair_adjacent_to in H_in.
    apply in_adjacent_exclude_in_exlude in H_in.
    move: H_in => [H_in H_adj].
    apply in_failed_exclude in H_in.
    move: H_in => [H_in H_in'].
    have H_nin: ~ In n (map tot_map_name failed).
      rewrite -(tot_map_name_inverse_inv n).
      exact: not_in_failed_not_in.
    apply tot_adjacent_to_fst_snd in H_adj.
    rewrite tot_map_name_inverse_inv in H_adj.
    have H_inn: In n ns'.
      apply (Permutation_in n) in H_pm => //.
      rewrite -(tot_map_name_inverse_inv n).
      exact: in_failed_in.
    exact: in_in_adj_map_pair.
  exact: in_map2snd_snd.
- case: x => n m0 H_in.
  have H_eq' := in_map2snd_snd _ _ adjacent_to adjacent_to_dec _ _ _ _ H_in.
  rewrite /= in H_eq'.
  rewrite H_eq'.
  rewrite H_eq' in H_in.
  apply in_map2snd_related_in in H_in.
  move: H_in => [H_adj H_in].
  rewrite -(tot_map_name_inverse_inv n) in H_adj.
  apply tot_adjacent_to_fst_snd in H_adj.
  apply in_exclude_not_in_failed_map in H_in.
  move: H_in => [H_in_f H_in].
  apply not_in_map_not_in_failed in H_in_f.
  have H_in_n: In (tot_map_name_inv n) ns.
    apply Permutation_sym in H_pm.
    apply (Permutation_in n) in H_pm => //.
    apply: tot_map_name_in.
    by rewrite tot_map_name_inverse_inv.
  apply: (@in_pt_map_map_pair m) => //; first by move => nm; apply in_map2snd_snd.
  apply adjacent_in_in_msg => //.
  exact: not_in_failed_in_exclude.
Qed.

Lemma pt_map_map_pair_eq :
  forall m m' h failed,
  pt_map_msg m = Some m' ->
  Permutation 
    (filterMap pt_map_name_msg (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed nodes))))
    (map2snd m' (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) nodes))).
Proof using overlay_map_congr name_map_bijective.
move => m m' h failed H_eq.
apply pt_nodup_perm_map_map_pair_perm => //; first exact: no_dup_nodes.
apply Permutation_sym.
exact: permutation_nodes.
Qed.

Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd msg_map}.

Theorem step_ordered_failure_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_ordered_failure _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_ordered_failure _ _ overlay_snd fail_msg_snd (map tot_map_name failed, pt_map_onet net) (map tot_map_name failed', pt_map_onet net') (filterMap pt_map_trace_ev tr) \/ 
    pt_map_onet net' = pt_map_onet net /\ failed = failed' /\ filterMap pt_map_trace_ev tr = [].
Proof using overlay_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_step.
invcs H_step.
- destruct (pt_map_msg m) eqn:?.
    left.
    rewrite /pt_map_onet /=.
    apply (@StepOrderedFailure_deliver _ _ _ _ _ _ _ _ m0 (filterMap pt_map_msg ms) (filterMap pt_map_output out) (pt_map_data d) (filterMap pt_map_name_msg l) (tot_map_name from) (tot_map_name to)).
    * rewrite /= 2!tot_map_name_inv_inverse /=.
      find_rewrite.
      rewrite /=.
      destruct (pt_map_msg _) eqn:?; rewrite Heqo in Heqo0 => //.
      by inversion Heqo.
    * exact: not_in_failed_not_in.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ Heqo)  /pt_mapped_net_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by find_inversion.
    * by rewrite /= pt_map_update_eq collate_pt_map_update2_eq.
    * by rewrite filterMap_pt_map_trace_ev_outputs_eq.
  right.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ Heqo H5.
  rewrite filterMap_pt_map_trace_ev_outputs_eq /= H_out /=.
  split => //.
  rewrite /pt_map_onet /= pt_map_update_eq H_eq_d collate_pt_map_update2_eq H_ms /=.
  set nwP1 := update2 _ _ _ _ _.
  set nwS1 := update _ _ _ _.
  set nwP2 := fun _ _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 {nwS1 nwS2}.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.  
  have H_eq_p: nwP1 = nwP2.
    rewrite /nwP1 /nwP2 /=.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move: H_dec => [H_eq_from H_eq_to].
    rewrite -H_eq_from -H_eq_to /= 2!tot_map_name_inv_inverse H3 /=.
    case H_m': (pt_map_msg _) => [m'|] //.
    by rewrite H_m' in Heqo.
  by rewrite H_eq_s H_eq_p.
- case H_i: (pt_map_input _) => [inp'|].
    left.
    apply (@StepOrderedFailure_input _ _ _ _ (tot_map_name h) _ _ _ _ (filterMap pt_map_output out) inp' (pt_map_data d) (filterMap pt_map_name_msg l)).
    * exact: not_in_failed_not_in.
    * rewrite /=.
      have H_q := pt_input_handlers_some h inp (onwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      find_rewrite.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * by rewrite /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
    * by rewrite filterMap_pt_map_trace_ev_outputs_eq.
  right.
  rewrite /= /pt_map_onet /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) H_i H4.
  rewrite filterMap_pt_map_trace_ev_outputs_eq H_o /=.
  split => //.
  rewrite pt_map_update_eq /= H_d.
  rewrite collate_pt_map_eq H_l /=.
  set nwS1 := update _ _ _ _.
  set nwS2 := fun n => pt_map_data _.
  have H_eq_n: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.
  by rewrite H_eq_n.
- left.
  rewrite /pt_map_onet /=.  
  set l := map2snd _ _.
  have H_nd: NoDup (map fst (filterMap pt_map_name_msg l)).
    rewrite /pt_map_name_msg /=.
    rewrite /l {l}.
    apply NoDup_map_snd_fst.
      apply (@nodup_pt_map msg_fail); first exact: in_map2snd_snd.
      apply NoDup_map2snd.
      apply NoDup_remove_all.
      exact: no_dup_nodes.
    move => nm nm' H_in H_in'.
    by rewrite (pt_map_in_snd  _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
  apply: StepOrderedFailure_fail => //.
  * exact: not_in_failed_not_in.
  * rewrite /= /l collate_pt_map_eq /=.
    by rewrite (NoDup_Permutation_collate_eq _ _ name_eq_dec _ _ _ _ H_nd (pt_map_map_pair_eq msg_fail h failed pt_fail_msg_fst_snd)).
Qed.

Corollary step_ordered_failure_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_ordered_failure_star _ _ overlay_fst fail_msg_fst step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ overlay_snd fail_msg_snd step_ordered_failure_init (map tot_map_name failed, pt_map_onet net) (filterMap pt_map_trace_ev tr).
Proof using overlay_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net failed tr H_step.
remember step_ordered_failure_init as y in *.
have H_eq_f: failed = fst (failed, net) by [].
have H_eq_n: net = snd (failed, net) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_n {H_eq_n}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_ordered_failure_init /= /pt_map_onet /=.
  rewrite -pt_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_ordered_failure_pt_mapped_simulation_1 in H.
rewrite filterMap_app.
case: H => H.
  have H_trans := refl_trans_1n_trace_trans IHH_step1.
  apply: H_trans.
  rewrite -(app_nil_r (filterMap pt_map_trace_ev _)).
  apply: (@RT1nTStep _ _ _ _ (map tot_map_name failed'', pt_map_onet net'')) => //.
  exact: RT1nTBase.
move: H => [H_eq_n [H_eq_f H_eq]].
by rewrite H_eq_n -H_eq_f H_eq app_nil_r.
Qed.

Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.
Context {new_msg_map_congr : NewMsgParamsPartialMapCongruency new_msg_fst new_msg_snd msg_map}.

Definition pt_map_odnet (net : @ordered_dynamic_network _ multi_fst) : @ordered_dynamic_network _ multi_snd :=
  {| odnwNodes := map tot_map_name net.(odnwNodes) ;
     odnwPackets := fun src dst => filterMap pt_map_msg (net.(odnwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     odnwState := fun n => match net.(odnwState) (tot_map_name_inv n) with
                         | None => None
                         | Some d => Some (pt_map_data d)
                         end |}.

Lemma collate_ls_pt_map_eq :
  forall ns f h m m',
    pt_map_msg m = Some m' ->
    (fun src dst => filterMap pt_map_msg (collate_ls name_eq_dec ns f h m (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate_ls name_eq_dec (map tot_map_name ns) (fun src dst => filterMap pt_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name h) m'.
Proof using name_map_bijective.
elim => //=.
move => n ns IH f h m m' H_eq.
rewrite /= (IH _ _ _  m') //=.
rewrite 2!tot_map_name_inv_inverse /=.
set f1 := fun _ _ => _.
set f2 := update2 _ _ _ _ _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  have H_eq' := pt_map_msg_update2 f (f n h ++ [m]) h n.
  rewrite filterMap_app in H_eq'.
  by rewrite H_eq' /= H_eq.
by rewrite H_eq_f.
Qed.

Theorem step_ordered_dynamic_failure_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ overlay_fst new_msg_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ overlay_snd new_msg_snd fail_msg_snd (map tot_map_name failed, pt_map_odnet net) (map tot_map_name failed', pt_map_odnet net') (filterMap pt_map_trace_ev tr) \/ 
    pt_map_odnet net' = pt_map_odnet net /\ failed = failed' /\ filterMap pt_map_trace_ev tr = [].
Proof using overlay_map_congr new_msg_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_nd H_step.
invcs H_step.
- left.
  rewrite /pt_map_odnet.
  apply (@StepOrderedDynamicFailure_start _ _ _ _ _ _ _ _ (tot_map_name h)) => /=; first exact: not_in_failed_not_in.
  set p1 := fun _ _ => _.
  set p2 := collate_ls _ _ _ _ _.
  set s1 := fun _ => _.
  set s2 := update _ _ _ _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2 /update {s1 s2}.
    apply functional_extensionality => n.
    rewrite -pt_init_handlers_eq.
    break_match_goal.
      break_if; break_if; try by congruence.
      - by repeat find_rewrite; repeat find_rewrite_lem tot_map_name_inv_inverse.
      - by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
      - by find_rewrite.
    break_if; break_if; (try by congruence); last by find_rewrite.
    by repeat find_rewrite; repeat find_rewrite_lem tot_map_name_inv_inverse.
  rewrite H_eq_s /s2 {s1 s2 H_eq_s}.
  have H_eq_p: p1 = p2.
    rewrite /p1 /p2 {p1 p2}.    
    rewrite (collate_ls_pt_map_eq _ _ _ _ pt_new_msg_fst_snd) /=.
    rewrite collate_pt_map_eq.
    set f1 := fun _ _ => _.    
    set c1 := collate _ _ _ _.
    set c2 := collate _ _ _ _.
    set f'1 := map tot_map_name _.
    set f'2 := filter_rel _ (tot_map_name h) _.
    have H_c: c1 = c2.
      rewrite /c1 /c2 {c1 c2}.
      apply: NoDup_Permutation_collate_eq; last first.
        rewrite /pt_map_name_msg.
        apply: pt_nodup_perm_map_map_pair_perm => //.
        by rewrite pt_new_msg_fst_snd.
      rewrite /pt_map_name_msg /=.
      apply: NoDup_map_snd_fst => //.
        apply (@nodup_pt_map msg_new); first exact: in_map2snd_snd.
        apply: NoDup_map2snd.
        exact: NoDup_remove_all.
      move => nm nm' H_in H_in'.
      apply (@pt_map_in_snd msg_new _ _ _ _ pt_new_msg_fst_snd) in H_in.
      apply (@pt_map_in_snd msg_new _ _ _ _ pt_new_msg_fst_snd) in H_in'.
      by rewrite H_in H_in'.
    rewrite H_c {H_c}.
    suff H_suff: f'1 = f'2 by rewrite H_suff.
    rewrite /f'1 /f'2.
    elim (odnwNodes net) => /=; first by rewrite 2!remove_all_nil.
    move => n ns.
    set mn := tot_map_name n.
    set mns := map _ ns.
    set mfailed' := map _ failed'.
    move => IH.
    have H_cn := remove_all_cons name_eq_dec failed' n ns.
    have H_cn' := remove_all_cons name_eq_dec mfailed' mn mns.
    unfold mn, mns, mfailed' in *.
    repeat break_or_hyp; repeat break_and; repeat find_rewrite => //=.
    * by find_apply_lem_hyp not_in_failed_not_in.
    * by find_apply_lem_hyp in_failed_in.
    * case: adjacent_to_dec => H_dec; case adjacent_to_dec => H_dec' => //=.
      + by rewrite IH.
      + by find_apply_lem_hyp tot_adjacent_to_fst_snd.
      + by find_apply_lem_hyp tot_adjacent_to_fst_snd.
  by rewrite H_eq_p.
- destruct (pt_map_msg m) eqn:?.
    left.
    rewrite /pt_map_odnet /=.
    apply (@StepOrderedDynamicFailure_deliver _ _ _ _ _ _ _ _ _ m0 (filterMap pt_map_msg ms) (filterMap pt_map_output out) (pt_map_data d) (pt_map_data d') (filterMap pt_map_name_msg l) (tot_map_name from) (tot_map_name to)).
    * exact: not_in_failed_not_in.
    * exact: in_failed_in. 
    * by rewrite /= tot_map_name_inv_inverse /= H5.
    * rewrite /= 2!tot_map_name_inv_inverse /=.
      find_rewrite.
      by rewrite /= Heqo.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ Heqo) /pt_mapped_net_handlers /=.
      repeat break_let.
      by tuple_inversion.
    * set u1 := fun _ => if _ is None then _ else _.
      set u2 := update _ _ _ _.
      rewrite collate_pt_map_update2_eq.
      suff H_suff: u1 = u2 by rewrite H_suff.
      rewrite /u1 /u2 /update /=.
      apply functional_extensionality => n.
      repeat break_if; try by congruence.
        rewrite -(tot_map_name_inverse_inv n) in n0.
        by rewrite e in n0.
      find_rewrite.
      by find_rewrite_lem tot_map_name_inv_inverse.
    * by rewrite filterMap_pt_map_trace_ev_outputs_eq.
- right.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ Heqo H7.
  rewrite filterMap_pt_map_trace_ev_outputs_eq H_out /=.
  split => //.
  rewrite /pt_map_odnet /= collate_pt_map_update2_eq H_ms /=.
  set nwP1 := update2 _ _ _ _ _.
  set nwP2 := fun _ _ => _ _.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 {nwS1 nwS2}.
    apply functional_extensionality => n.
    rewrite /update /=.
    case: name_eq_dec => H_dec //.
    by rewrite H_dec H5 H_eq_d.
  have H_eq_p: nwP1 = nwP2.
    rewrite /nwP1 /nwP2 /=.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    rewrite /update2 /=.
    break_if => //.
    break_and.
    by rewrite -H -H0 2!tot_map_name_inv_inverse H6 /= Heqo.
  by rewrite H_eq_s H_eq_p.
- case H_i: (pt_map_input _) => [inp'|].
    left.
    apply (@StepOrderedDynamicFailure_input _ _ _ _ _ (tot_map_name h) _ _ _ _ (filterMap pt_map_output out) inp' (pt_map_data d) (pt_map_data d') (filterMap pt_map_name_msg l)).
    * exact: not_in_failed_not_in.
    * exact: in_failed_in. 
    * by rewrite /pt_map_odnet /= tot_map_name_inv_inverse H5.
    * have H_q := pt_input_handlers_some h inp d H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      find_rewrite.
      by rewrite H_q.
    * rewrite /= /pt_map_odnet /= collate_pt_map_eq.
      set u1 := fun _ => if _ is None then _ else _.
      set u2 := update _ _ _ _.
      suff H_suff: u1 = u2 by rewrite H_suff.
      rewrite /u1 /u2 /update /=.
      apply functional_extensionality => n.
      repeat break_if; try by congruence.
        rewrite -(tot_map_name_inverse_inv n) in n0.
        by rewrite e in n0.
      find_rewrite.
      by find_rewrite_lem tot_map_name_inv_inverse.
    * by rewrite filterMap_pt_map_trace_ev_outputs_eq.
  right.
  rewrite /= /pt_map_odnet /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp d H_i H6.
  rewrite filterMap_pt_map_trace_ev_outputs_eq H_o /=.
  split => //=.
  rewrite collate_pt_map_eq H_l /=.
  set nwS1 := fun n => if _ is None then _ else _.
  set nwS2 := fun n => if _ is None then _ else _.
  have H_eq_n: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case: name_eq_dec => H_dec //.
    by rewrite H_dec H5 H_d.
  by rewrite H_eq_n.
- left.
  rewrite /pt_map_odnet /=.
  set l := map2snd _ _.
  have H_nd': NoDup (map (fun nm => fst nm) (filterMap pt_map_name_msg l)).
    rewrite /pt_map_name_msg /=.
    rewrite /l {l}.
    apply NoDup_map_snd_fst.
      apply (@nodup_pt_map msg_fail); first exact: in_map2snd_snd.
      apply NoDup_map2snd.
      exact: NoDup_remove_all.
    move => nm nm' H_in H_in'.
    by rewrite (pt_map_in_snd  _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
  apply: StepOrderedDynamicFailure_fail => //.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in.
  * rewrite /=.
    rewrite /l collate_pt_map_eq.
    have H_pm := pt_nodup_perm_map_map_pair_perm _ h failed H_nd (Permutation_refl (map tot_map_name (odnwNodes net))) pt_fail_msg_fst_snd.
    have H_pm' := H_pm _ _ fail_msg_map_congr.
    have H_eq := NoDup_Permutation_collate_eq  _ _ _ _ _ _ _ H_nd' H_pm'.
    by rewrite H_eq.
Qed.

Corollary step_ordered_dynamic_failure_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ overlay_fst new_msg_fst fail_msg_fst step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ overlay_snd new_msg_snd fail_msg_snd step_ordered_dynamic_failure_init (map tot_map_name failed, pt_map_odnet net) (filterMap pt_map_trace_ev tr).
Proof using overlay_map_congr new_msg_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net failed tr H_step.
remember step_ordered_dynamic_failure_init as y in *.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 2.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_ordered_dynamic_failure_init /= /step_ordered_failure_init.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
destruct x'.
destruct x''.
rewrite /=.
find_apply_lem_hyp step_ordered_dynamic_failure_pt_mapped_simulation_1; last by move: H_step1; apply: ordered_dynamic_nodes_no_dup.
simpl in *.
rewrite filterMap_app.
case: H => H.
  have H_trans := refl_trans_1n_trace_trans IHH_step1.
  apply: H_trans.
  rewrite -(app_nil_r (filterMap pt_map_trace_ev _)).
  apply: (@RT1nTStep _ _ _ _ (map tot_map_name l0, pt_map_odnet o0)) => //.
  exact: RT1nTBase.
move: H => [H_eq_n [H_eq_f H_eq]].
by rewrite H_eq_n -H_eq_f H_eq app_nil_r.
Qed.

Lemma in_msg_filterMap_pt_map_msg :
  forall l m' m0,
    pt_map_msg m0 = Some m' ->
    In m0 l ->
    In m' (filterMap pt_map_msg l).
Proof using.
elim => //.
move => m0 l IH.
move => m1 m2 H_eq H_in.
case: H_in => H_in.
  rewrite H_in /= H_eq.
  by left.
have IH' := IH _ _ H_eq H_in.
rewrite /=.
by break_match; first by right.
Qed.

Hypothesis pt_map_msg_injective : 
  forall m0 m1 m, pt_map_msg m0 = Some m -> pt_map_msg m1 = Some m -> m0 = m1.

Lemma in_filterMap_pt_map_msg_in_msg :
  forall l m0 m1,
    pt_map_msg m0 = Some m1 ->
    In m1 (filterMap pt_map_msg l) ->
    In m0 l.
Proof using pt_map_msg_injective.
elim => //=.
move => m0 l IH.
move => m1 m2 H_eq H_in.
have IH' := IH _ _ H_eq.
break_match; last first.
  right.
  exact: IH'.
have IH'' := IH _ _ Heqo.
case: H_in => H_in; last first.
  right.
  exact: IH'.
rewrite H_in in IH'' Heqo.
left.
move: Heqo H_eq.
exact: pt_map_msg_injective.
Qed.

Lemma in_all_before_pt_map_msg :
  forall l m0 m1 m'0 m'1,
    pt_map_msg m0 = Some m'0 ->
    pt_map_msg m1 = Some m'1 ->
    before_all m'0 m'1 (filterMap pt_map_msg l) ->
    before_all m0 m1 l.
Proof using.
elim => //=.
move => m l IH m0 m1 m'0 m'1 H_eq H_eq' H_bef.
break_match; simpl in *.
  case: H_bef => H_bef.
    left.
    move => H_in.
    case: H_bef.
    move: H_eq H_in.
    exact: in_msg_filterMap_pt_map_msg.
  break_and.
  right.
  split; last first.
    move: H0.
    exact: IH.
  move => H_eq_m.
  rewrite H_eq_m in H_eq'.
  rewrite Heqo in H_eq'.
  by find_injection.
right.
split; last first.
  move: H_bef.
  exact: IH.
by congruence.
Qed.

Lemma count_occ_filterMap_pt_map_msg_eq :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  count_occ msg_eq_dec (filterMap pt_map_msg l) m' = count_occ msg_eq_dec l m0.
Proof using pt_map_msg_injective.
elim => //=.
move => m l IH m' m0 H_eq.
break_if.
  repeat find_rewrite.
  rewrite /=.
  break_if => //.
  have IH' := IH _ _ H_eq.
  by rewrite IH'.
have IH' := IH _ _ H_eq.
rewrite -IH'.
break_match => //.
rewrite /=.
break_if => //.
case: n.
find_rewrite.
move: Heqo H_eq.
exact: pt_map_msg_injective.
Qed.

Lemma hd_error_filterMap_pt_map_msg :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  hd_error l = Some m0 ->
  hd_error (filterMap pt_map_msg l) = Some m'.
Proof using.
case => //=.
move => m l m' m0 H_eq H_eq'.
find_injection.
by break_match.
Qed.

End PartialMapSimulations.
