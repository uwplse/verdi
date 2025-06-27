From Verdi Require Import Verdi DynamicNetLemmas.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Sorting.Permutation Sumbool.
From Verdi Require Import Ssrexport.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Class BaseParamsTotalMap (P0 : BaseParams) (P1 : BaseParams) :=
  {
    tot_map_data : @data P0 -> @data P1 ;
    tot_map_input : @input P0 -> @input P1 ;
    tot_map_output : @output P0 -> @output P1
  }.

Class MultiParamsNameTotalMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : MultiParams B1)  :=
  {
    tot_map_name : @name B0 P0 -> @name B1 P1 ;
    tot_map_name_inv : @name B1 P1 -> @name B0 P0
  }.

Class MultiParamsNameTotalMapBijective `(M : MultiParamsNameTotalMap) : Prop :=
  {
    tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n ;
    tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n ;
  }.

Class MultiParamsMsgTotalMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : MultiParams B1) :=
  {
    tot_map_msg : @msg B0 P0 -> @msg B1 P1
  }.

Section TotalMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgTotalMap multi_fst multi_snd}.

Definition tot_map_name_msgs :=
  map (fun nm => (tot_map_name (fst nm), tot_map_msg (snd nm))).

Definition tot_mapped_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).

Definition tot_mapped_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).

End TotalMapDefs.

Class MultiParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (B : BaseParamsTotalMap B0 B1)
  (N : MultiParamsNameTotalMap P0 P1)
  (P : MultiParamsMsgTotalMap P0 P1) : Prop :=
  {
    tot_init_handlers_eq : forall n,
      tot_map_data (init_handlers n) = init_handlers (tot_map_name n) ;
    tot_net_handlers_eq : forall me src m st,
      tot_mapped_net_handlers me src m st =
      net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st) ;
    tot_input_handlers_eq : forall me inp st,
      tot_mapped_input_handlers me inp st =
      input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st)
  }.

Class FailureParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailureParams P0) (F1 : FailureParams P1)
  (B : BaseParamsTotalMap B0 B1) : Prop :=
  {
    tot_reboot_eq : forall d, tot_map_data (reboot d) = reboot (tot_map_data d)
  }.

Class NameOverlayParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (O0 : NameOverlayParams P0) (O1 : NameOverlayParams P1)
  (N : MultiParamsNameTotalMap P0 P1) : Prop :=
  {
    tot_adjacent_to_fst_snd : forall n n',
      adjacent_to n n' <-> adjacent_to (tot_map_name n) (tot_map_name n')
  }.

Class FailMsgParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailMsgParams P0) (F1 : FailMsgParams P1)
  (P : MultiParamsMsgTotalMap P0 P1) : Prop :=
  {
    tot_fail_msg_fst_snd : msg_fail = tot_map_msg msg_fail
  }.

Class NewMsgParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (N0 : NewMsgParams P0) (N1 : NewMsgParams P1)
  (P : MultiParamsMsgTotalMap P0 P1) : Prop :=
  {
    tot_new_msg_fst_snd : msg_new = tot_map_msg msg_new
  }.

Section TotalMapBijective.

Context `{MB : MultiParamsNameTotalMapBijective}.

Lemma tot_map_name_injective : 
  forall n n', tot_map_name n = tot_map_name n' -> n = n'.
Proof using MB.
move => n n'.
case (name_eq_dec n n') => H_dec //.
move => H_eq.
case: H_dec.
by rewrite -(tot_map_name_inv_inverse n) H_eq tot_map_name_inv_inverse.
Qed.

End TotalMapBijective.

Section TotalMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgTotalMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsTotalMapCongruency base_map name_map msg_map}.

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
  {| nwPackets := map tot_map_packet net.(nwPackets) ;
     nwState := fun n => tot_map_data (net.(nwState) (tot_map_name_inv n)) |}.

Lemma tot_map_update_eq :
  forall f d h,
    (fun n : name => tot_map_data (update name_eq_dec f h d (tot_map_name_inv n))) =
    update name_eq_dec (fun n : name => tot_map_data (f (tot_map_name_inv n))) (tot_map_name h) (tot_map_data d).
Proof using name_map_bijective.
move => net d h.
apply functional_extensionality => n.
rewrite /update /=.
repeat break_match => //.
- by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
- by find_rewrite; find_rewrite_lem tot_map_name_inv_inverse.
Qed.

Corollary tot_map_update_packet_eq :
forall f p d,
  (fun n : name => tot_map_data (update name_eq_dec f (pDst p) d (tot_map_name_inv n))) =
  (update name_eq_dec (fun n : name => tot_map_data (f (tot_map_name_inv n))) (pDst (tot_map_packet p)) (tot_map_data d)).
Proof using name_map_bijective.
move => f.
case => src dst m d.
exact: tot_map_update_eq.
Qed.

Lemma tot_map_packet_map_eq :
  forall l h,
    map tot_map_packet (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l) =
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (tot_map_name_msgs l).
Proof using.
elim => //=.
case => /= n m' l IH h.
by rewrite IH.
Qed.

Lemma tot_init_handlers_fun_eq : 
    init_handlers = fun n : name => tot_map_data (init_handlers (tot_map_name_inv n)).
Proof using name_map_bijective multi_map_congr msg_map.
apply functional_extensionality => n.
by rewrite tot_init_handlers_eq tot_map_name_inverse_inv.
Qed.

Lemma tot_map_trace_occ_inv : 
  forall tr n ol,
    map tot_map_trace_occ tr = [(n, inr ol)] -> 
    exists n', exists lo, tr = [(n', inr lo)] /\ tot_map_name n' = n /\ map tot_map_output lo = ol.
Proof using.
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
Proof using name_map_bijective.
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
inversion H_eq.
find_apply_lem_hyp tot_map_name_injective.
repeat find_rewrite.
by exists h; exists inp; exists out.
Qed.

Theorem step_async_tot_mapped_simulation_1 :
  forall net net' tr,
    @step_async _ multi_fst net net' tr ->
    @step_async _ multi_snd (tot_map_net net) (tot_map_net net') (map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_congr.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  rewrite /tot_map_trace_occ /=.
  have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by case: p H_eq H_hnd H_eq' => src dst m H_eq H_hnd H_eq'.
  apply (@StepAsync_deliver _ _ _ _ _ (map tot_map_packet ms) (map tot_map_packet ms') (map tot_map_output out) (tot_map_data d) (tot_map_name_msgs l)).
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
    rewrite 2!map_app.
    destruct p.
    by rewrite tot_map_packet_map_eq.
- move => h net net' out inp d l H_hnd H_eq.
  apply (@StepAsync_input _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
    rewrite /=.
    have H_q := tot_input_handlers_eq h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  rewrite /= H_eq /= /tot_map_net /=.
  by rewrite -tot_map_update_eq map_app tot_map_packet_map_eq.
Qed.

Corollary step_async_tot_mapped_simulation_star_1 :
  forall net tr,
    @step_async_star _ multi_fst step_async_init net tr ->
    @step_async_star _ multi_snd step_async_init (tot_map_net net) (map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_congr.
move => net tr H_step.
remember step_async_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_async_init /= /tot_map_net /=.
  rewrite tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
find_apply_lem_hyp step_async_tot_mapped_simulation_1.
rewrite map_app.
match goal with
| H : step_async_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H)
end.
rewrite -(app_nil_r (map _ _)).
apply: (@RT1nTStep _ _ _ _ (tot_map_net x'')) => //.
exact: RT1nTBase.
Qed.

Hypothesis tot_map_output_injective :
  forall o o', tot_map_output o = tot_map_output o' -> o = o'.

Theorem step_async_tot_mapped_simulation_2 :
  forall net net' out mnet mout,
      @step_async _ multi_snd net net' out ->
      tot_map_net mnet = net ->
      map tot_map_trace_occ mout = out ->
      exists mnet', @step_async _ multi_fst mnet mnet' mout /\
      tot_map_net mnet' = net'.
Proof using tot_map_output_injective name_map_bijective multi_map_congr.
move => net net' out mnet mout H_step H_eq H_eq'.
invcs H_step.
- destruct p.
  rewrite /tot_map_net /=.
  destruct mnet.
  rewrite /=.
  match goal with
  | H : map tot_map_packet _ = _ |- _ =>
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (Net.pDst p) l' ++ pks1 ++ pks2 ; nwState := update name_eq_dec nwState (Net.pDst p) d' |}.
  split.
  * match goal with
    | H : _ = map tot_map_trace_occ _ |- _ =>
      have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H)
    end.
    rewrite H_eq_mout.
    have H_eq_dst: n' = Net.pDst p.
      rewrite -(tot_map_name_inv_inverse n') H_eq_n.
      destruct p.
      find_inversion.
      by rewrite tot_map_name_inv_inverse.
    rewrite H_eq_dst.
    apply (@StepAsync_deliver _ _ _ _ _ pks1 pks2 _ d' l') => //=.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    simpl in *.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
    rewrite H_eq_body in H_eq_hnd.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ =>
      rewrite -H_eq_n tot_map_name_inv_inverse H_eq_dst in H ;
        rewrite H in H_eq_hnd
    end.
    find_inversion.
    find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
    by symmetry.
  * rewrite /= /update /=.
    have H_eq_dst: tot_map_name (Net.pDst p) = pDst by destruct p; find_inversion.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; find_inversion.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; find_inversion.
    rewrite 2!map_app.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    simpl in *.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ =>
      rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H;
        rewrite H in H_eq_hnd
    end.
    find_inversion; clean.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2.
      elim l' => //=.
      case => /= n' m' l0 IH.
      rewrite IH.
      by find_rewrite.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      repeat break_if => //.
      + find_reverse_rewrite. 
        by find_rewrite_lem tot_map_name_inverse_inv.
      + find_rewrite. 
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_sw.
- rewrite /tot_map_net /=.
  destruct mnet.
  simpl in *.
  match goal with
  | H: _ = map tot_map_trace_occ _ |- _ => 
    have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H)
  end.
  have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h' inp' (nwState h').
  rewrite /tot_mapped_input_handlers in H_q.
  repeat break_let.
  rewrite H_eq_n H_eq_inp in H_q.
  match goal with
    | H: input_handlers _ _ (tot_map_data (_ (tot_map_name_inv h))) = _ |- _ => 
      rewrite -{2}H_eq_n tot_map_name_inv_inverse in H;
        rewrite H in H_q
  end.
  find_inversion.
  find_inversion.
  exists ({| nwPackets := send_packets h' l0 ++ nwPackets ; nwState := update name_eq_dec nwState h' d0 |}).
  split.
  * apply (@StepAsync_input _ _ _ _ _ _ _ d0 l0) => //=.
    find_rewrite.
    suff H_suff: l1 = out' by rewrite H_suff.
    by find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
  * rewrite /= map_app.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := update _ _ _ _.
    have H_eq_nwp: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {nwP1 nwP2}.
      elim l0 => //=.
      case => /= n m l' IH.
      by rewrite IH.
    have H_eq_nws: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      rewrite /update /=.
      apply functional_extensionality => n.
      repeat break_if => //.
      + find_reverse_rewrite. 
        by find_rewrite_lem tot_map_name_inverse_inv.
      + find_rewrite.
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_nwp H_eq_nws.
Qed.

Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.
Context {fail_map_congr : FailureParamsTotalMapCongruency fail_fst fail_snd base_map}.

Lemma not_in_failed_not_in :
  forall n failed,
    ~ In n failed ->
    ~ In (tot_map_name n) (map tot_map_name failed).
Proof using name_map_bijective.
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
Proof using.
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
Proof using name_map_bijective.
move => h.
elim => //=.
move => n failed IH.
repeat break_if => //.
- by find_rewrite.
- by find_apply_lem_hyp tot_map_name_injective.
- by rewrite /= IH.
Qed.

Theorem step_failure_tot_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_failure _ _ fail_fst (failed, net) (failed', net') tr ->
    @step_failure _ _ fail_snd (map tot_map_name failed, tot_map_net net) (map tot_map_name failed', tot_map_net net') (map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_congr fail_map_congr.
move => net net' failed failed' tr H_step.
invcs H_step.
- have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by destruct p.
  apply (@StepFailure_deliver _ _ _ _ _ _ _ (map tot_map_packet xs) (map tot_map_packet ys) _ (tot_map_data d) (tot_map_name_msgs l)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * destruct p.
    exact: not_in_failed_not_in.
  * destruct p.
    simpl in *.
    have H_q := tot_net_handlers_eq pDst pSrc pBody (nwState net pDst).
    rewrite /tot_mapped_net_handlers in H_q.
    find_rewrite.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= -tot_map_update_packet_eq /= /tot_map_net /=.
    destruct p.
    by rewrite 2!map_app tot_map_packet_map_eq.
- apply (@StepFailure_input _ _ _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /=.
    have H_q := tot_input_handlers_eq h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= in H_q.
    find_rewrite.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= /tot_map_net /= -tot_map_update_eq.
    by rewrite map_app tot_map_packet_map_eq.
- apply (@StepFailure_drop _ _ _ _ _ _ (tot_map_packet p) (map tot_map_packet xs) (map tot_map_packet ys)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * by rewrite /tot_map_net /= map_app.
- apply (@StepFailure_dup _ _ _ _ _ _ (tot_map_packet p) (map tot_map_packet xs) (map tot_map_packet ys)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * by rewrite /tot_map_net /= map_app.
- exact: StepFailure_fail.
- eapply (@StepFailure_reboot _ _ _ (tot_map_name h)).
  * exact: in_failed_in.
  * by rewrite remove_tot_map_eq.
  * by rewrite /tot_map_net /= tot_map_update_eq tot_reboot_eq tot_map_name_inv_inverse.
Qed.

Corollary step_failure_tot_mapped_simulation_star_1 :
  forall net failed tr,
    @step_failure_star _ _ fail_fst step_failure_init (failed, net) tr ->
    @step_failure_star _ _ fail_snd step_failure_init (map tot_map_name failed, tot_map_net net) (map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_congr fail_map_congr.
move => net failed tr H_step.
remember step_failure_init as y in *.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 2.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_failure_init /= /step_async_init /tot_map_net /= tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
destruct x'.
destruct x''.
rewrite /=.
find_apply_lem_hyp step_failure_tot_mapped_simulation_1.
rewrite map_app.
match goal with
| H : step_failure_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H)
end.
rewrite -(app_nil_r (map tot_map_trace_occ _)).
apply (@RT1nTStep _ _ _ _ (map tot_map_name l0, tot_map_net n0)) => //.
exact: RT1nTBase.
Qed.

Lemma map_eq_name_eq_eq :
  forall l l', map tot_map_name l = map tot_map_name l' -> l = l'.
Proof using name_map_bijective.
elim.
case => //=.
move => n l IH.
case => //=.
move => n' l' H_eq.
inversion H_eq.
find_apply_lem_hyp tot_map_name_injective.
find_eapply_lem_hyp IH.
by repeat find_rewrite.
Qed.

Theorem step_failure_tot_mapped_simulation_2 :
  forall net net' failed failed' out mnet mfailed mfailed' mout,
      @step_failure _ _ fail_snd (failed, net) (failed', net') out ->
      tot_map_net mnet = net ->
      map tot_map_name mfailed = failed ->
      map tot_map_name mfailed' = failed' ->
      map tot_map_trace_occ mout = out ->
      exists mnet', @step_failure _ _ fail_fst (mfailed, mnet) (mfailed', mnet') mout /\
      tot_map_net mnet' = net'.
Proof using tot_map_output_injective name_map_bijective multi_map_congr fail_map_congr.
move => net net' failed failed' out mnet mfailed mfailed' mout H_step H_eq_net H_eq_f H_eq_f' H_eq_out.
invcs H_step.
- destruct p.
  rewrite /tot_map_net /=.
  destruct mnet.
  simpl in *.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (Net.pDst p) l' ++ pks1 ++ pks2 ; nwState := update name_eq_dec nwState (Net.pDst p) d' |}.
  split.
  * match goal with
    | H : _ = map tot_map_trace_occ _ |- _ => 
      have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H)
    end.
    rewrite H_eq_mout.
    have H_eq_dst: n' = Net.pDst p.
      rewrite -(tot_map_name_inv_inverse n') H_eq_n.
      destruct p.
      simpl in *.
      find_inversion.
      by rewrite tot_map_name_inv_inverse.
    rewrite H_eq_dst.
    match goal with
    | H: map tot_map_name _ = map tot_map_name _ |- _ =>
      apply map_eq_name_eq_eq in H; rewrite H
    end.
    apply (@StepFailure_deliver _ _ _ _ _ _ _ pks1 pks2 _ d' l') => //=.
      rewrite -H_eq_dst => H_in.
      find_apply_lem_hyp in_failed_in.
      by find_rewrite_lem H_eq_n.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
    rewrite H_eq_body in H_eq_hnd.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => 
      rewrite -H_eq_n tot_map_name_inv_inverse H_eq_dst in H ;
        rewrite H in H_eq_hnd
    end.
    find_inversion.
    find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
    by symmetry.
  * rewrite /= /update /=.
    have H_eq_dst: tot_map_name (Net.pDst p) = pDst by destruct p; simpl in *; find_inversion.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
    rewrite 2!map_app.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    simpl in *.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => 
      rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H;
        rewrite H in H_eq_hnd
    end.
    find_inversion; clean.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2.
      elim l' => //=.
      case => /= n' m' l0 IH.
      rewrite IH.
      by find_rewrite.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      repeat break_if => //.
      + find_reverse_rewrite. 
        by find_rewrite_lem tot_map_name_inverse_inv.
      + find_rewrite. 
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_sw.
- rewrite /tot_map_net /=.
  destruct mnet.
  match goal with
  | H: _ = map tot_map_trace_occ _ |- _ => 
    have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H)
  end.
  have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h' inp' (nwState h').
  rewrite /tot_mapped_input_handlers in H_q.
  repeat break_let.
  rewrite H_eq_n H_eq_inp in H_q.
  match goal with
    | H: input_handlers _ _ (tot_map_data (_ (tot_map_name_inv h))) = _ |- _ => 
      rewrite -{2}H_eq_n tot_map_name_inv_inverse in H ;
        rewrite H in H_q
    end.
  inversion H_q.
  simpl in *.
  find_apply_lem_hyp map_eq_name_eq_eq.   
  exists ({| nwPackets := send_packets h' l0 ++ nwPackets ; nwState := update name_eq_dec nwState h' d0 |}).
  split.
  * rewrite H_eq_mout.
    match goal with
    | H: mfailed = _ |- _ => rewrite H
    end.
    apply (@StepFailure_input _ _ _ _ _ _ _ _ _ d0 l0) => //.      
      move => H_in.
      apply in_failed_in in H_in.
      by rewrite H_eq_n in H_in.
    rewrite /= Heqp.
    suff H_suff: l1 = out' by rewrite H_suff.
    match goal with
    | H: map tot_map_output _ = _ |- _ => rewrite -H_eq_out in H
    end.    
    by find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
  * rewrite /= map_app.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := update _ _ _ _.
    have H_eq_nwp: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {Heqp H_q nwP1 nwP2}.
      elim l0 => //=.
      case => /= n m l' IH.
      by rewrite H_eq_n IH.
    have H_eq_nws: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      rewrite /update /=.
      apply functional_extensionality => n.
      rewrite -H_eq_n.
      repeat break_if => //.
      + match goal with
        | H: _ = h' , H': _ <> tot_map_name h' |- _ => 
          rewrite -H in H'
        end.
        by find_rewrite_lem tot_map_name_inverse_inv.
      + match goal with
        | H: n = _ , H': tot_map_name_inv n <> _ |- _ => 
          rewrite H in H'
        end.
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_nwp H_eq_nws.
- destruct mout => //.
  find_apply_lem_hyp map_eq_name_eq_eq.
  find_reverse_rewrite.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p' pks2 H_eq_pks H_eq_pks2.
  inversion H_eq_pks2.
  rewrite -H_eq_pks1.
  exists {| nwPackets := pks1 ++ pks2 ; nwState := nwState mnet |}.
  split; first exact: (@StepFailure_drop _ _ _ _ _ _ p' pks1 pks2).
  by rewrite /tot_map_net /= map_app.
- destruct mout => //.
  find_apply_lem_hyp map_eq_name_eq_eq.
  find_rewrite.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p' pks2 H_eq_pks H_eq_pks2.
  inversion H_eq_pks2.
  rewrite -H_eq_pks1.
  exists {| nwPackets := p' :: pks1 ++ p' :: pks2 ; nwState := nwState mnet |}.
  split; first exact: (@StepFailure_dup _ _ _ _ _ _ p' pks1 pks2).
  by rewrite /tot_map_net /= map_app.  
- destruct mout => //.
  destruct mfailed' => //.
  simpl in *.
  find_inversion.
  find_apply_lem_hyp map_eq_name_eq_eq.
  find_rewrite.
  exists mnet => //.
  split => //.
  exact: StepFailure_fail.
- destruct mout => //.
  find_copy_apply_lem_hyp in_split.
  break_exists.
  match goal with
  | H: map tot_map_name _ = _ |- _ =>
    have [mns1 [mns2 [H_eq_mns [H_eq_mns1 H_eq_mns2]]]] := map_eq_inv _ _ _ _ H
  end.
  destruct mns2 => //.
  exists {| nwPackets := nwPackets mnet ; 
       nwState := update name_eq_dec (nwState mnet) n (reboot (nwState mnet n)) |}.
  split.
  * apply (@StepFailure_reboot _ _ _ n) => //.
    + rewrite H_eq_mns.
      apply in_or_app.
      by right; left.
    + inversion H_eq_mns2.
      have H_eq: remove name_eq_dec h (map tot_map_name mfailed) = map tot_map_name (remove name_eq_dec n mfailed).
        elim mfailed => //=.
        move => n' l IH.
        repeat break_if => //.
        + by find_reverse_rewrite; find_apply_lem_hyp tot_map_name_injective.
        + by find_reverse_rewrite; find_reverse_rewrite.
        + by rewrite /= IH.
      match goal with
      | H: _ = remove _ _ _ |- _ => rewrite H_eq in H
      end.
      by find_apply_lem_hyp map_eq_name_eq_eq.
  * rewrite /tot_map_net /=.
    inversion H_eq_mns2.
    by rewrite tot_map_update_eq tot_map_name_inv_inverse tot_reboot_eq.
Qed.

Lemma nodup_to_map_name :
  forall ns, NoDup ns ->
        NoDup (map tot_map_name ns).
Proof using name_map_bijective.
elim => /=; first by move => H_nd; exact: NoDup_nil.
move => n ns IH H_nd.
inversion H_nd.
find_apply_lem_hyp IH.
by apply NoDup_cons; first exact: not_in_failed_not_in.  
Qed.

Lemma permutation_nodes :
  Permutation nodes (map tot_map_name nodes).
Proof using name_map_bijective.
apply: NoDup_Permutation; last split.
- exact: no_dup_nodes.
- apply nodup_to_map_name.
  exact: no_dup_nodes.
- move => H_in.
  set x' := tot_map_name_inv x.
  have H_in' := all_names_nodes x'. 
  apply in_split in H_in'.
  move: H_in' => [ns1 [ns2 H_eq]].
  rewrite H_eq map_app /= /x'.
  apply in_or_app.
  right; left.
  by rewrite tot_map_name_inverse_inv.
- move => H_in.
  exact: all_names_nodes.
Qed.

Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Lemma tot_map_in_snd :
forall h m ns nm,
   In nm
     (map
        (fun nm0 : name * msg =>
         (tot_map_name (fst nm0), tot_map_msg (snd nm0)))
        (map2snd m (filter_rel adjacent_to_dec h ns))) ->
   snd nm = tot_map_msg m.
Proof using.
move => h m.
elim => //=.
move => n ns IH.
case: (adjacent_to_dec _ _) => H_dec /=.
  case => n' m' H_in.
  case: H_in => H_in.
    by inversion H_in.
  exact: IH.
exact: IH.
Qed.

Lemma tot_map_in_in :
  forall n m l,
  (forall nm, In nm l -> snd nm = m) ->
  ~ In (n, m) l ->
  ~ In (tot_map_name n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l).
Proof using name_map_bijective.
move => n m.
elim => //=.
case => /= n' m' l IH H_eq H_in.
move => H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  have H_nm := H_eq (n', m').
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
  apply: H_eq.
  by right.
move => H_in_nm.
case: H_in.
by right.
Qed.

Lemma msg_in_map :
  forall m l n m',
    (forall nm, In nm l -> snd nm = m) ->
    In (tot_map_name n, tot_map_msg m') (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l) ->
    tot_map_msg m' = tot_map_msg m.
Proof using.
move => m.
elim => //=.
case => /= n m' l IH n' m0 H_in H_in_map.
have H_in_f := H_in (n, m').
rewrite /= in H_in_f.
case: H_in_map => H_in_map.
  inversion H_in_map.
  rewrite H_in_f //.
  by left.
move: H_in_map.
apply: IH.
move => nm H_in'.
apply: H_in.
by right.
Qed.

Lemma nodup_tot_map :
  forall m nms,
  (forall nm, In nm nms -> snd nm = m) ->
  NoDup nms ->
  NoDup (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) nms).
Proof using name_map_bijective.
move => m'.
elim => /=.
  move => H_fail H_nd.
  exact: NoDup_nil.
case => n m l IH H_fail H_nd.
inversion H_nd.
rewrite /=.
apply NoDup_cons.
  have H_f := H_fail (n, m).
  rewrite /= in H_f.
  move => H_in.
   have H_inf := @msg_in_map m' _ _ _ _ H_in.
   rewrite H_inf in H_in.
     contradict H_in.
     apply tot_map_in_in.
       move => nm H_in_nm.
       apply: H_fail.
       by right.
     rewrite H_f // in H1.
     by left.
   move => nm H_in_f.
   apply: H_fail.
   by right.
apply: IH => //.
move => nm H_in_nm.
apply: H_fail.
by right.
Qed.

Lemma in_tot_map_name :
forall m l n,
  (forall nm, In nm l -> snd nm = m) ->
  In (n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l) ->
  In (tot_map_name_inv n, m) l.
Proof using name_map_bijective.
move => m.
elim => //=.
case => /= n m' l IH n' H_in H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  rewrite tot_map_name_inv_inverse.
  have H_nm := H_in (n, m').
  rewrite -H_nm /=; first by left.
  by left.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma in_map_pair_adjacent_to :
  forall (m : @msg _ multi_fst) ns failed h n,
    In (tot_map_name_inv n, m) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns))) ->
    In (tot_map_name_inv n) (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)).
Proof using.
move => m.
elim => //= [|n l IH] failed h n'; first by rewrite remove_all_nil.
have H_cn := remove_all_cons name_eq_dec failed n l.
break_or_hyp; break_and; find_rewrite; first exact: IH.
rewrite /=.
case: (adjacent_to_dec _ _) => H_dec' /=.
  move => H_in.
  case: H_in => H_in.
    inversion H_in.
    by left.
  right.
  exact: IH.
exact: IH.
Qed.

Lemma in_adjacent_exclude_in_exlude :
  forall ns failed n h,
    In (tot_map_name_inv n) (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)) ->
    In (tot_map_name_inv n) (remove_all name_eq_dec failed ns) /\ adjacent_to h (tot_map_name_inv n).
Proof using.
elim => [|n l IH] failed n' h; first by rewrite remove_all_nil.
have H_cn := remove_all_cons name_eq_dec failed n l.
break_or_hyp; break_and; find_rewrite; first exact: IH.
rewrite /=.
case: (adjacent_to_dec _ _) => /= H_dec'.
  move => H_in.
  case: H_in => H_in.
    rewrite {1}H_in -{4}H_in.
    split => //.
    by left.
  apply IH in H_in.
  move: H_in => [H_eq H_in].
  split => //.
  by right.
move => H_in.
apply IH in H_in.
move: H_in => [H_eq H_in].
split => //.
by right.
Qed.

Lemma in_failed_exclude :
  forall ns failed n,
    In (tot_map_name_inv n) (remove_all name_eq_dec failed ns) ->
    ~ In (tot_map_name_inv n) failed /\ In (tot_map_name_inv n) ns.
Proof using.
elim => [|n ns IH] failed n'; first by rewrite remove_all_nil.
have H_cn := remove_all_cons name_eq_dec failed n ns.
break_or_hyp; break_and; find_rewrite.
  move => H_in.
  apply IH in H_in.
  move: H_in => [H_in H_in'].
  split => //.
  by right.
move => H_in.
case: H_in => H_in.
  rewrite -{1}H_in {2}H_in.
  split => //.
  by left.
apply IH in H_in.
move: H_in => [H_in H_in'].
split => //.
by right.
Qed.

Lemma in_in_adj_map_pair :
  forall (m : msg) ns failed n h,
    In n ns ->
    ~ In n (map tot_map_name failed) ->
    adjacent_to h n ->
    In (n, m)
     (map2snd m
        (filter_rel adjacent_to_dec h
           (remove_all name_eq_dec (map tot_map_name failed) ns))).
Proof using.
move => m.
elim => //=.
move => n ns IH failed n' h.
set mfailed := map _ failed.
move => H_in H_in' H_adj.
have H_cn := remove_all_cons name_eq_dec mfailed n ns.
break_or_hyp; break_and; find_rewrite.
  break_or_hyp => //.
  exact: IH.
case: H_in => H_in.
  rewrite H_in.
  rewrite /=.
  case (adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  by left.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  right.
  exact: IH.
exact: IH.
Qed.

Lemma in_exclude_not_in_failed_map :
  forall ns n failed,
  In n (remove_all name_eq_dec (map tot_map_name failed) ns) ->
  ~ In n (map tot_map_name failed) /\ In n ns.
Proof using.
elim => [|n ns IH] n' failed; first by rewrite remove_all_nil.
set mfailed := map _ failed.
have H_cn := remove_all_cons name_eq_dec mfailed n ns.
break_or_hyp; break_and; find_rewrite.
  move => H_in.
  apply IH in H_in.
  move: H_in => [H_nin H_in].
  split => //.
  by right.
rewrite /=.
move => H_in.
case: H_in => H_in.
  rewrite H_in.
  subst.
  split => //.
  by left.
apply IH in H_in.
move: H_in => [H_nin H_in].
split => //.
by right.
Qed.

Lemma not_in_map_not_in_failed :
  forall failed n,
    ~ In n (map tot_map_name failed) ->
    ~ In (tot_map_name_inv n) failed.
Proof using name_map_bijective.
elim => //=.
move => n ns IH n' H_in H_in'.
case: H_in' => H_in'.
  case: H_in.
  left.
  by rewrite H_in' tot_map_name_inverse_inv.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma in_tot_map_msg :
  forall m l n,
    (forall nm, In nm l -> snd nm = m) ->
    In (tot_map_name_inv n, m) l ->
    In (n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l).
Proof using name_map_bijective.
move => m.
elim => //=.
case => n m' /= l IH n' H_in H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  left.
  by rewrite tot_map_name_inverse_inv.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma adjacent_in_in_msg :
  forall (m : @msg base_fst multi_fst) ns n h,
    adjacent_to h (tot_map_name_inv n) ->
    In (tot_map_name_inv n) ns ->
    In (tot_map_name_inv n, m) (map2snd m (filter_rel adjacent_to_dec h ns)).
Proof using.
move => m.
elim => //=.
move => n ns IH n' h H_adj H_in.
case: (adjacent_to_dec _ _) => H_dec; case: H_in => H_in.
- rewrite /=.
  left.
  by rewrite H_in.
- rewrite /=.
  right.
  exact: IH.
- by rewrite H_in in H_dec.
- exact: IH.
Qed.

Lemma not_in_failed_in_exclude :
  forall ns n failed,
  ~ In (tot_map_name_inv n) failed ->
  In (tot_map_name_inv n) ns ->
  In (tot_map_name_inv n) (remove_all name_eq_dec failed ns).
Proof using.
elim => //=.
move => n ns IH n' failed H_in H_in'.
have H_cn := remove_all_cons name_eq_dec failed n ns.
break_or_hyp; break_and; find_rewrite; break_or_hyp => //=. 
- exact: IH.
- by left.
- right; exact: IH.
Qed.

Lemma tot_map_name_in : 
  forall ns n,
    In (tot_map_name n) (map tot_map_name ns) ->
    In n ns.
Proof using name_map_bijective.
elim => //=.
move => n' ns IH n H_in.
case: H_in => H_in.
  left.
  exact: tot_map_name_injective.
right.
exact: IH.
Qed.

Lemma nodup_perm_map_map_pair_perm :
  forall h m failed ns ns',
  NoDup ns ->
  Permutation (map tot_map_name ns) ns' ->
  Permutation 
    (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)))) 
    (map2snd (tot_map_msg m) (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) ns'))).
Proof using overlay_map_congr name_map_bijective.
move => h m failed ns ns' H_nd H_pm.
apply NoDup_Permutation; last split.
- apply (@nodup_tot_map m); first exact: in_map2snd_snd.
  apply NoDup_map2snd.
  by apply NoDup_remove_all.
- apply NoDup_map2snd.
  apply NoDup_remove_all.
  move: H_pm.
  apply: NoDup_Permutation_NoDup.
  exact: nodup_to_map_name.
- case: x => n m' H_in.
  have H_eq := tot_map_in_snd _ _ _ _ H_in.
  rewrite /= in H_eq.
  rewrite H_eq in H_in.
  rewrite H_eq {H_eq}.
  apply in_tot_map_name in H_in.
    apply in_map2snd_related_in in H_in.
    move: H_in => [H_adj H_in].
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
- case: x => n m' H_in.
  have H_eq := in_map2snd_snd _ _ adjacent_to adjacent_to_dec _ _ _ _ H_in.
  rewrite /= in H_eq.
  rewrite H_eq.
  rewrite H_eq in H_in.
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
  apply in_tot_map_msg; first by move => nm; apply in_map2snd_snd.
  apply: adjacent_in_in_msg => //.
  exact: not_in_failed_in_exclude.
Qed.

Lemma map_map_pair_eq :
  forall h m failed,
  Permutation 
    (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed nodes)))) 
    (map2snd (tot_map_msg m) (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) nodes))).
Proof using overlay_map_congr name_map_bijective.
move => h m failed.
apply nodup_perm_map_map_pair_perm; first exact: no_dup_nodes.
apply Permutation_sym.
exact: permutation_nodes.
Qed.

Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsTotalMapCongruency fail_msg_fst fail_msg_snd msg_map}.

Lemma map_msg_fail_eq_nodup :
  forall h failed ns ns',
  NoDup ns ->
  Permutation (map tot_map_name ns) ns' ->
   Permutation 
    (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd msg_fail (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)))) 
    (map2snd msg_fail (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) ns'))).
Proof using overlay_map_congr name_map_bijective fail_msg_map_congr.
move => h failed.
rewrite tot_fail_msg_fst_snd.
exact: nodup_perm_map_map_pair_perm.
Qed.

Lemma map_msg_fail_eq :
  forall h failed,
   Permutation 
    (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd msg_fail (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed nodes)))) 
    (map2snd msg_fail (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) nodes))).
Proof using overlay_map_congr name_map_bijective fail_msg_map_congr.
move => h failed.
rewrite tot_fail_msg_fst_snd.
exact: map_map_pair_eq.
Qed.

Definition tot_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd :=
  {| onwPackets := fun src dst => map tot_map_msg (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     onwState := fun n => tot_map_data (onet.(onwState) (tot_map_name_inv n)) |}.

Lemma map_msg_update2 : 
  forall f ms to from,
    (fun src dst => map tot_map_msg (update2 name_eq_dec f from to ms (tot_map_name_inv src) (tot_map_name_inv dst))) =
    update2 name_eq_dec (fun src0 dst0 : name => map tot_map_msg (f (tot_map_name_inv src0) (tot_map_name_inv dst0)))
        (tot_map_name from) (tot_map_name to) (map tot_map_msg ms).
Proof using name_map_bijective.
move => f ms to from.
apply functional_extensionality => src.
apply functional_extensionality => dst.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec; case (sumbool_and _ _ _ _) => H_dec' //.
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

Lemma collate_tot_map_eq :
  forall f h l,
    (fun src dst => map tot_map_msg (collate name_eq_dec h f l (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate name_eq_dec (tot_map_name h) (fun src dst => map tot_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name_msgs l).
Proof using name_map_bijective.
move => f h l.
elim: l h f => //.
case => n m l IH h f.
rewrite /= IH /=.
rewrite 2!tot_map_name_inv_inverse /=.
set f1 := fun _ _ => _.
set f2 := update2 _ _ _ _ _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  have H_eq := map_msg_update2 f (f h n ++ [m]) n h.
  rewrite map_app in H_eq.
  by rewrite H_eq.
by rewrite H_eq_f.
Qed.

Lemma collate_tot_map_update2_eq :
  forall f from to ms l,
    (fun src dst => map tot_map_msg
            (collate name_eq_dec to (update2 name_eq_dec f from to ms) l
               (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate name_eq_dec (tot_map_name to)
            (update2 name_eq_dec
               (fun src dst : name =>
                map tot_map_msg
                  (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name from)
               (tot_map_name to) (map tot_map_msg ms)) (tot_map_name_msgs l).
Proof using name_map_bijective.
move => f from to ms l.
rewrite -map_msg_update2.
by rewrite collate_tot_map_eq.
Qed.

Definition tot_map_trace (e : @name _ multi_fst * (@input base_fst + (@output base_fst))) :=
match e with
| (n, inl i) => (tot_map_name n, inl (tot_map_input i))
| (n, inr o) => (tot_map_name n, inr (tot_map_output o))
end.

Lemma map_tot_map_trace_eq :
  forall out to,
    map tot_map_trace (map2fst to (map inr out)) =
    map2fst (tot_map_name to) (map inr (map tot_map_output out)).
Proof using.
elim => //=.
move => o out IH to.
by rewrite IH.
Qed.

Theorem step_ordered_failure_tot_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_ordered_failure _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_ordered_failure _ _ overlay_snd fail_msg_snd (map tot_map_name failed, tot_map_onet net) (map tot_map_name failed', tot_map_onet net') (map tot_map_trace tr).
Proof using overlay_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_step.
invcs H_step.
- rewrite /tot_map_onet /=.
  apply (@StepOrderedFailure_deliver _ _ _ _ _ _ _ _ (tot_map_msg m) (map tot_map_msg ms) (map tot_map_output out) (tot_map_data d) (tot_map_name_msgs l) (tot_map_name from) (tot_map_name to)).
  * by rewrite /tot_map_net /= 2!tot_map_name_inv_inverse /= H3.
  * exact: not_in_failed_not_in.
  * rewrite /= tot_map_name_inv_inverse -tot_net_handlers_eq /tot_mapped_net_handlers /=.
    repeat break_let.
    by find_inversion.
  * by rewrite /= tot_map_update_eq collate_tot_map_update2_eq.
  * by rewrite map_tot_map_trace_eq.
- rewrite /tot_map_onet /=.
  apply (@StepOrderedFailure_input _ _ _ _ (tot_map_name h) _ _ _ _ (map tot_map_output out) (tot_map_input inp) (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /= tot_map_name_inv_inverse -tot_input_handlers_eq /tot_mapped_input_handlers.
    repeat break_let.
    by find_inversion.
  * by rewrite /= /tot_map_onet /= tot_map_update_eq collate_tot_map_eq.
  * by rewrite map_tot_map_trace_eq.
- rewrite /tot_map_onet /=.
  set l := map2snd _ _.
  have H_nd: NoDup (map fst (tot_map_name_msgs l)).
    rewrite /tot_map_name_msgs /=.
    rewrite /l {l} /=.
    eapply NoDup_map_snd_fst.
      apply (@nodup_tot_map msg_fail); first exact: in_map2snd_snd.
      apply NoDup_map2snd.
      apply NoDup_remove_all.
      exact: no_dup_nodes.
    move => nm nm' H_in H_in'.
    have H_fail := tot_map_in_snd _ _ _ _ H_in.
    have H_fail' := tot_map_in_snd _ _ _ _ H_in'.
    by rewrite H_fail H_fail'.
  have H_pm := map_msg_fail_eq h failed.
  have H_eq := NoDup_Permutation_collate_eq  _ _ name_eq_dec _ _ _ _ H_nd H_pm.
  rewrite /l /tot_map_name_msgs in H_eq.
  apply: StepOrderedFailure_fail.
  * exact: not_in_failed_not_in.
  * rewrite /=.
    rewrite /l collate_tot_map_eq /tot_map_name_msgs.
    by rewrite H_eq.
Qed.

Corollary step_ordered_failure_tot_mapped_simulation_star_1 :
  forall net failed tr,
    @step_ordered_failure_star _ _ overlay_fst fail_msg_fst step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ overlay_snd fail_msg_snd step_ordered_failure_init (map tot_map_name failed, tot_map_onet net) (map tot_map_trace tr).
Proof using overlay_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net failed tr H_step.
remember step_ordered_failure_init as y in *.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 2.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_ordered_failure_init /= /step_ordered_init /tot_map_onet /= tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
destruct x'.
destruct x''.
rewrite /=.
find_apply_lem_hyp step_ordered_failure_tot_mapped_simulation_1.
rewrite map_app.
match goal with
| H : step_ordered_failure_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H)
end.
rewrite -(app_nil_r (map tot_map_trace _)).
apply (@RT1nTStep _ _ _ _ (map tot_map_name l0, tot_map_onet o0)) => //.
exact: RT1nTBase.
Qed.

Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.
Context {new_msg_map_congr : NewMsgParamsTotalMapCongruency new_msg_fst new_msg_snd msg_map}.

Definition tot_map_odnet (net : @ordered_dynamic_network _ multi_fst) : @ordered_dynamic_network _ multi_snd :=
  {| odnwNodes := map tot_map_name net.(odnwNodes) ;
     odnwPackets := fun src dst => map tot_map_msg (net.(odnwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     odnwState := fun n => 
                   match net.(odnwState) (tot_map_name_inv n) with
                   | None => None
                   | Some d => Some (tot_map_data d)
                   end |}.

Lemma collate_ls_tot_map_eq :
  forall ns f h m,
    (fun src dst => map tot_map_msg (collate_ls name_eq_dec ns f h m (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate_ls name_eq_dec (map tot_map_name ns) (fun src dst => map tot_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name h) (tot_map_msg m).
Proof using name_map_bijective.
elim => //=.
move => n ns IH f h m.
rewrite /= IH /=.
rewrite 2!tot_map_name_inv_inverse /=.
set f1 := fun _ _ => _.
set f2 := update2 _ _ _ _ _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  have H_eq := map_msg_update2 f (f n h ++ [m]) h n.
  rewrite map_app in H_eq.
  by rewrite H_eq.
by rewrite H_eq_f.
Qed.

Lemma collate_ls_tot_map_update2_eq :
  forall ns f h m from to ms,
    (fun src dst => map tot_map_msg
            (collate_ls name_eq_dec ns (update2 name_eq_dec f from to ms) h m
               (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate_ls name_eq_dec (map tot_map_name ns)
            (update2 name_eq_dec (fun src dst : name => map tot_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst)))
                     (tot_map_name from) (tot_map_name to) (map tot_map_msg ms))
            (tot_map_name h) (tot_map_msg m).
Proof using name_map_bijective.
move => ns f h m from to ms.
rewrite -map_msg_update2.
by rewrite collate_ls_tot_map_eq.
Qed.

Theorem step_ordered_dynamic_failure_tot_mapped_simulation_1 :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ overlay_fst new_msg_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ overlay_snd new_msg_snd fail_msg_snd (map tot_map_name failed, tot_map_odnet net) (map tot_map_name failed', tot_map_odnet net') (map tot_map_trace tr).
Proof using overlay_map_congr new_msg_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_nd H_step.
invcs H_step.
- rewrite /tot_map_odnet /=.
  apply (@StepOrderedDynamicFailure_start _ _ _ _ _ _ _ _ (tot_map_name h)) => /=; first exact: not_in_failed_not_in.
  set p1 := fun _ _ => _.
  set p2 := collate_ls _ _ _ _ _.
  set s1 := fun _ => _.
  set s2 := update _ _ _ _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2 /update {s1 s2}.
    apply functional_extensionality => n.
    rewrite -tot_init_handlers_eq.
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
    rewrite collate_ls_tot_map_eq /=.
    rewrite collate_tot_map_eq.
    rewrite tot_new_msg_fst_snd.
    set f1 := fun _ _ => _.    
    set c1 := collate _ _ _ _.
    set c2 := collate _ _ _ _.
    set f'1 := map tot_map_name _.
    set f'2 := filter_rel _ (tot_map_name h) _.
    have H_c: c1 = c2.
      rewrite /c1 /c2 {c1 c2}.
      apply: NoDup_Permutation_collate_eq; last first.
        rewrite /tot_map_name_msgs.
        by apply: nodup_perm_map_map_pair_perm; last exact: Permutation_refl.
      rewrite /tot_map_name_msgs /=.
      apply: NoDup_map_snd_fst => //.
        apply (@nodup_tot_map msg_new); first exact: in_map2snd_snd.
        apply: NoDup_map2snd.
        exact: NoDup_remove_all.
      move => nm nm' H_in H_in'.
      apply tot_map_in_snd in H_in.
      apply tot_map_in_snd in H_in'.
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
- rewrite /tot_map_odnet /=.
  apply (@StepOrderedDynamicFailure_deliver _ _ _ _ _ _ _ _ _ (tot_map_msg m) (map tot_map_msg ms) (map tot_map_output out) (tot_map_data d) (tot_map_data d') (tot_map_name_msgs l) (tot_map_name from) (tot_map_name to)) => //=.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in. 
  * rewrite tot_map_name_inv_inverse.
    by break_match; congruence.
  * rewrite 2!tot_map_name_inv_inverse.
    by find_rewrite.
  * rewrite -tot_net_handlers_eq /tot_mapped_net_handlers.
    repeat break_let.
    by repeat tuple_inversion.
  * set u1 := fun _ => if _ is None then _ else _.
    set u2 := update _ _ _ _.
    rewrite collate_tot_map_update2_eq.
    suff H_suff: u1 = u2 by rewrite H_suff.
    rewrite /u1 /u2 /update /=.
    apply functional_extensionality => n.
    repeat break_if; try by congruence.
      rewrite -(tot_map_name_inverse_inv n) in n0.
      by rewrite e in n0.
    find_rewrite.
    by find_rewrite_lem tot_map_name_inv_inverse.
  * by rewrite map_tot_map_trace_eq.
- rewrite /tot_map_odnet /=.
  apply (@StepOrderedDynamicFailure_input _ _ _ _ _ (tot_map_name h) _ _ _ _ (map tot_map_output out) (tot_map_input inp) (tot_map_data d) (tot_map_data d') (tot_map_name_msgs l)) => //=.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in. 
  * rewrite tot_map_name_inv_inverse.
    by break_match; congruence.
  * rewrite /= -tot_input_handlers_eq /tot_mapped_input_handlers.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite collate_tot_map_eq.
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
  * by rewrite map_tot_map_trace_eq.
- rewrite /tot_map_odnet /=.  
  set l := map2snd _ _.
  have H_nd': NoDup (map (fun nm => fst nm) (tot_map_name_msgs l)).
    rewrite /tot_map_name_msgs /=.
    rewrite /l {l}.
    apply NoDup_map_snd_fst.
      apply (@nodup_tot_map msg_fail); first exact: in_map2snd_snd.
      apply NoDup_map2snd.
      exact: NoDup_remove_all.
    move => nm nm' H_in H_in'.
    have H_fail := tot_map_in_snd _ _ _ _ H_in.
    have H_fail' := tot_map_in_snd _ _ _ _ H_in'.
    by rewrite H_fail H_fail'.
  have H_pm := map_msg_fail_eq_nodup h failed H_nd (Permutation_refl (map tot_map_name (odnwNodes net))).
  have H_eq := NoDup_Permutation_collate_eq  _ _ name_eq_dec _ _ _ _ H_nd' H_pm.
  rewrite /l /tot_map_name_msgs in H_eq.
  apply: StepOrderedDynamicFailure_fail.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in. 
  * rewrite /=.
    rewrite /l collate_tot_map_eq /tot_map_name_msgs.
    by rewrite H_eq.
Qed.

Corollary step_ordered_dynamic_failure_tot_mapped_simulation_star_1 :
  forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ overlay_fst new_msg_fst fail_msg_fst step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ overlay_snd new_msg_snd fail_msg_snd step_ordered_dynamic_failure_init (map tot_map_name failed, tot_map_odnet net) (map tot_map_trace tr).
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
find_apply_lem_hyp step_ordered_dynamic_failure_tot_mapped_simulation_1.
  rewrite map_app.
  match goal with
  | H : step_ordered_dynamic_failure_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H)
  end.
  rewrite -(app_nil_r (map tot_map_trace _)).
  apply (@RT1nTStep _ _ _ _ (map tot_map_name l0, tot_map_odnet o0)) => //.
  exact: RT1nTBase.
move: H_step1.
exact: ordered_dynamic_nodes_no_dup.
Qed.

End TotalMapSimulations.
