Require Import StructTact.Util.
Require Import Verdi.Verdi.

Require Import FunctionalExtensionality.

Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.

Require Import Cheerios.Cheerios.
Require Import Verdi.SerializedMsgParams.

Require Import mathcomp.ssreflect.ssreflect.

Section SerializedMsgCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {orig_name_overlay_params : NameOverlayParams orig_multi_params}.
  Context {orig_fail_msg_params : FailMsgParams orig_multi_params}.
  Context {orig_new_msg_params : NewMsgParams orig_multi_params}.
  Context {orig_msg_serializer : Serializer msg}.

  Definition serialize_packet p :=
    @mkPacket _ serialized_multi_params
              (@pSrc _ orig_multi_params p)
              (pDst p)
              (serialize_top (serialize (pBody p))).

  Definition serialize_net (net : @network _ orig_multi_params) : (@network _ serialized_multi_params) :=
    @mkNetwork _ serialized_multi_params (map serialize_packet (nwPackets net)) net.(nwState).

  Definition serialize_onet (net : @ordered_network _ orig_multi_params) : (@ordered_network _ serialized_multi_params) :=
    @mkONetwork _ serialized_multi_params (fun src dst => map (fun v => serialize_top (serialize v)) (net.(onwPackets) src dst)) net.(onwState).

  Definition serialize_odnet (net : @ordered_dynamic_network _ orig_multi_params) : (@ordered_dynamic_network _ serialized_multi_params) :=
    @mkODNetwork _ serialized_multi_params net.(odnwNodes) (fun src dst => map (fun v => serialize_top (serialize v)) (net.(odnwPackets) src dst)) net.(odnwState).

  Instance orig_multi_params_name_tot_map :
    MultiParamsNameTotalMap orig_multi_params serialized_multi_params :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

  Instance orig_multi_params_name_tot_map_bijective :
    MultiParamsNameTotalMapBijective orig_multi_params_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => eq_refl ;
    tot_map_name_inverse_inv := fun _ => eq_refl
  }.

  Instance orig_base_params_tot_map :
    BaseParamsTotalMap orig_base_params serialized_base_params :=
  {
    tot_map_data := id;
    tot_map_input := id;
    tot_map_output := id
  }.

  Instance orig_multi_params_tot_msg_map :
    MultiParamsMsgTotalMap orig_multi_params serialized_multi_params :=
  {
    tot_map_msg := fun v => serialize_top (serialize v)
  }.

  Instance orig_failure_params_tot_map_congruency : FailureParamsTotalMapCongruency orig_failure_params serialized_failure_params orig_base_params_tot_map :=
    {
      tot_reboot_eq := fun _ => eq_refl
    }.

  Instance orig_multi_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency orig_name_overlay_params serialized_name_overlay_params orig_multi_params_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

  Instance orig_multi_fail_msg_params_tot_map_congruency : FailMsgParamsTotalMapCongruency orig_fail_msg_params serialized_fail_msg_params orig_multi_params_tot_msg_map :=
  {
    tot_fail_msg_fst_snd := eq_refl
  }.

  Instance orig_multi_new_msg_params_tot_map_congruency : NewMsgParamsTotalMapCongruency orig_new_msg_params serialized_new_msg_params orig_multi_params_tot_msg_map :=
  {
    tot_new_msg_fst_snd := eq_refl
  }.

  Instance orig_multi_params_map_congruency :
    MultiParamsTotalMapCongruency orig_base_params_tot_map
      orig_multi_params_name_tot_map orig_multi_params_tot_msg_map :=
  {
    tot_init_handlers_eq := fun _ => eq_refl ;
    tot_net_handlers_eq := _ ;
    tot_input_handlers_eq := _
  }.
  Proof using.
  - move => me src m st.
    rewrite /tot_mapped_net_handlers /= /tot_map_name_msgs /= /id /=.
    repeat break_let.
    rewrite /serialized_net_handlers.
    rewrite serialize_deserialize_top_id.
    rewrite /serialize_handler_result.
    repeat break_let.
    find_injection.
    rewrite map_id.
    set l1 := map _ l.
    set l2 := map _ l.
    suff H_suff: l1 = l2 by rewrite H_suff.
    rewrite /l1 /l2.
    clear.
    elim: l => //=.
    move => p l IH.
    rewrite IH /= /serialize_name_msg_tuple /=.
    by break_let.
  - move => me inp st.
    rewrite /tot_mapped_input_handlers /=.
    repeat break_let.
    unfold serialized_input_handlers in *.
    rewrite /serialize_handler_result /id /tot_map_name_msgs /tot_map_name /= /id /=.
    repeat break_let.
    find_injection.
    rewrite map_id.
    set l1 := map _ l.
    set l2 := map _ l.
    suff H_suff: l1 = l2 by rewrite H_suff.
    rewrite /l1 /l2.
    clear.
    elim: l => //=.
    move => p l IH.
    rewrite IH /= /serialize_name_msg_tuple /=.
    by break_let.
  Qed.

  Lemma serialize_odnet_tot_map_odnet :
    forall net, serialize_odnet net = tot_map_odnet net.
  Proof using.
  move => net.
  rewrite /tot_map_odnet.
  rewrite /tot_map_name /= /id /= map_id.
  rewrite /serialize_odnet.
  set f := fun _ => match _ with _ => _ end.
  by have ->: odnwState net = f by rewrite /f; apply functional_extensionality => n; case: odnwState.
  Qed.

  Lemma step_async_serialize_simulation :
    forall net net' tr,
      @step_async _ orig_multi_params net net' tr ->
      @step_async _ serialized_multi_params (serialize_net net) (serialize_net net') tr.
  Proof using.
  move => net net' out H_step.
  apply step_async_tot_mapped_simulation_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.  
  rewrite /serialize_net.
  move: H_step.
  set fp := fun p => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  rewrite H_eq {H_eq fp}.
  set mp := fun e : name * _ => _.
  suff H_eq': map mp out = out by rewrite H_eq'.
  elim: out => //=.
  case => a.
  case => /= [i|o] l IH; rewrite IH //.
  by rewrite map_id.
  Qed.

  Lemma step_async_serialize_simulation_star :
    forall net tr,
      @step_async_star _ orig_multi_params step_async_init net tr ->
      @step_async_star _ serialized_multi_params step_async_init (serialize_net net) tr.
  Proof using.
  move => net tr H_step.
  apply step_async_tot_mapped_simulation_star_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  rewrite H_eq {H_eq fp}.
  set mp := fun e : name * _ => _.
  suff H_eq': map mp tr = tr by rewrite H_eq'.
  elim: tr => //=.
  case => a.
  case => /= [i|o] l IH; rewrite IH //.
  by rewrite map_id.
  Qed.

  Lemma step_failure_serialize_simulation :
    forall net net' failed failed' tr,
      @step_failure _ _ orig_failure_params (failed, net) (failed', net') tr ->
      @step_failure _ _ serialized_failure_params (failed, serialize_net net) (failed', serialize_net net') tr.
  Proof using.
  move => net net' failed failed' tr H_step.
  apply step_failure_tot_mapped_simulation_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  rewrite 2!map_id.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  rewrite H_eq {H_eq fp}.
  set mp := fun e : name * _ => _.
  suff H_eq': map mp tr = tr by rewrite H_eq'.
  elim: tr => //=.
  case => a.
  case => /= [i|o] l IH; rewrite IH //.
  by rewrite map_id.
  Qed.

  Lemma step_failure_serialize_simulation_star :
    forall net failed tr,
      @step_failure_star _ _ orig_failure_params step_failure_init (failed, net) tr ->
      @step_failure_star _ _ serialized_failure_params step_failure_init (failed, serialize_net net) tr.
  Proof using.
  move => net failed tr H_step.
  apply step_failure_tot_mapped_simulation_star_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  rewrite map_id.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  rewrite H_eq {H_eq fp}.
  rewrite /tot_map_trace_occ /=.
  set fp := fun e : name * _ => _.
  suff H_eq': map fp tr = tr by rewrite H_eq'.
  elim: tr => //=.
  case => a.
  case => /= [i|o] l IH; rewrite IH //.
  by rewrite map_id.
  Qed.

  Lemma step_ordered_failure_serialize_simulation :
  forall net net' failed failed' tr,
    @step_ordered_failure _ _ orig_name_overlay_params orig_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_failure _ _ serialized_name_overlay_params serialized_fail_msg_params (failed, serialize_onet net) (failed', serialize_onet net') tr.
  Proof using.
  move => net net' failed failed' tr H_step.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  have H_eq_tr: tr = map (@tot_map_trace _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /tot_map_trace /= /id /= {H_step}.
    elim: tr => //=.
    by case => a; case => [i|o] l IH; rewrite -IH.
  rewrite H_eq_tr.
  exact: step_ordered_failure_tot_mapped_simulation_1.
  Qed.

  Lemma step_ordered_failure_serialize_simulation_star :
  forall net failed tr,
    @step_ordered_failure_star _ _ orig_name_overlay_params orig_fail_msg_params step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ serialized_name_overlay_params serialized_fail_msg_params step_ordered_failure_init (failed, serialize_onet net) tr.
  Proof using.
  move => net failed tr H_st.
  have ->: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  have ->: tr = map (@tot_map_trace _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /tot_map_trace /= /id /= {H_st}.
    elim: tr => //=.
    by case => a; case => [i|o] l IH; rewrite -IH.
  exact: step_ordered_failure_tot_mapped_simulation_star_1.
  Qed.

  Lemma step_ordered_dynamic_failure_serialize_simulation :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params (failed, serialize_odnet net) (failed', serialize_odnet net') tr.
  Proof using.
  move => net net' failed failed' tr H_nd H_step.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  rewrite 2!serialize_odnet_tot_map_odnet.
  have ->: tr = map (@tot_map_trace _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /tot_map_trace /= /id /= {H_step}.
    elim: tr => //=.
    by case => a; case => [i|o] l IH; rewrite -IH.
  exact: step_ordered_dynamic_failure_tot_mapped_simulation_1.
  Qed.

  Lemma step_ordered_dynamic_failure_serialize_simulation_star :
  forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params step_ordered_dynamic_failure_init (failed, serialize_odnet net) tr.
  Proof using.
  move => net failed tr H_st.
  have ->: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite serialize_odnet_tot_map_odnet.
  have ->: tr = map (@tot_map_trace _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /tot_map_trace /= /id /= {H_st}.
    elim: tr => //=.
    by case => a; case => [i|o] l IH; rewrite -IH.
  exact: step_ordered_dynamic_failure_tot_mapped_simulation_star_1.
  Qed.

  Definition deserialize_packet (p : @packet _ serialized_multi_params) : option (@packet _ orig_multi_params) :=
    match deserialize_top deserialize (pBody p) with
    | None => None
    | Some body =>
      Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body)
    end.

  Definition deserialize_net (net: @network _ serialized_multi_params) :  (@network _ orig_multi_params) :=
    @mkNetwork _ orig_multi_params (filterMap deserialize_packet (nwPackets net)) net.(nwState).

  Definition deserialize_onet (net: @ordered_network _ serialized_multi_params) :  (@ordered_network _ orig_multi_params) :=
    @mkONetwork _ orig_multi_params (fun src dst => filterMap (fun m => match deserialize_top deserialize m with Some data => Some data | None => None end) (net.(onwPackets) src dst)) net.(onwState).

  Definition deserialize_odnet (net: @ordered_dynamic_network _ serialized_multi_params) :  (@ordered_dynamic_network _ orig_multi_params) :=
    @mkODNetwork _ orig_multi_params net.(odnwNodes) (fun src dst => filterMap (fun m => match deserialize_top deserialize m with Some data => Some data | None => None end) (net.(odnwPackets) src dst)) net.(odnwState).

  Lemma deserialize_serialize_net_id : forall net,
      deserialize_net (serialize_net net) = net.
  Proof using.
  case => ps nwS.
  rewrite /deserialize_net /serialize_net /=.
  set ps' := filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    rewrite /deserialize_packet.
    elim: ps => [|p ps IH] //=.
    rewrite serialize_deserialize_top_id IH.
    by case: p.
  by rewrite H_p.
  Qed.

  Lemma deserialize_serialize_onet_id : forall net,
      deserialize_onet (serialize_onet net) = net.
  Proof using.
  case => ps s.
  rewrite /deserialize_onet /serialize_onet /=.
  set ps' := fun _ _ => filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    elim: (ps src dst) => [|m ms IH] //=.
    by rewrite serialize_deserialize_top_id IH.
  by rewrite H_p.
  Qed.

  Lemma deserialize_serialize_odnet_id : forall net,
      deserialize_odnet (serialize_odnet net) = net.
  Proof using.
  case => ns ps s.
  rewrite /deserialize_odnet /serialize_odnet /=.
  set ps' := fun _ _ => filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.    
    elim: (ps src dst) => [|m ms IH] //=.
    by rewrite serialize_deserialize_top_id IH.
  by rewrite H_p.
  Qed.

  Instance multi_params_orig_name_tot_map :
    MultiParamsNameTotalMap serialized_multi_params orig_multi_params :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

  Instance multi_params_orig_name_tot_map_bijective :
    MultiParamsNameTotalMapBijective multi_params_orig_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => _ ;
    tot_map_name_inverse_inv := fun _ => _
  }.
  Proof using.
  - reflexivity.
  - reflexivity.
  Qed.

  Instance multi_orig_params_pt_msg_map : MultiParamsMsgPartialMap serialized_multi_params orig_multi_params :=
  {
    pt_map_msg := fun m => 
      match deserialize_top deserialize m with
      | Some data => Some data
      | None => None
      end   
  }.

  Instance multi_orig_base_params_pt_map : BaseParamsPartialMap serialized_base_params orig_base_params :=
  {
    pt_map_data := id;
    pt_map_input := fun i => Some i;
    pt_map_output := fun o => Some o
  }.

  Instance multi_orig_failure_params_pt_map_congruency : FailureParamsPartialMapCongruency serialized_failure_params orig_failure_params multi_orig_base_params_pt_map :=
  {
    pt_reboot_eq := fun _ => _
  }.
  Proof using.
    reflexivity.
  Qed.

  Instance multi_orig_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency serialized_name_overlay_params orig_name_overlay_params multi_params_orig_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => _
  }.
  Proof using.
    apply conj; auto.
  Qed.

  Instance multi_orig_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency serialized_fail_msg_params orig_fail_msg_params multi_orig_params_pt_msg_map :=
  {
    pt_fail_msg_fst_snd := _
  }.
  Proof using.
  rewrite /pt_map_msg /=.
  by rewrite serialize_deserialize_top_id.
  Qed.

  Instance multi_orig_new_msg_params_pt_map_congruency : NewMsgParamsPartialMapCongruency serialized_new_msg_params orig_new_msg_params multi_orig_params_pt_msg_map :=
  {
    pt_new_msg_fst_snd := _
  }.
  Proof using.
  rewrite /pt_map_msg /=.
  by rewrite serialize_deserialize_top_id.
  Qed.

  Instance multi_orig_params_pt_map_congruency : MultiParamsPartialMapCongruency multi_orig_base_params_pt_map multi_params_orig_name_tot_map multi_orig_params_pt_msg_map :=
  {
    pt_init_handlers_eq := fun _ => eq_refl ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
  Proof using.
  - move => me src mg st mg' H_eq.
    rewrite /pt_mapped_net_handlers.
    repeat break_let.
    rewrite /tot_map_name /= /id.
    rewrite /pt_map_msg /= in H_eq.
    rewrite /net_handlers /= /serialized_net_handlers in Heqp.
    move: H_eq Heqp.
    case H_m: (deserialize_top deserialize mg) => [m'|] => H_eq //.
    find_injection.
    rewrite /serialize_handler_result in Heqp.
    repeat break_let.
    find_injection.
    set sl2 := filterMap (fun _ => _) _.
    set sl1 := filterMap _ _.
    have H_eq: sl2 = l0.
      rewrite /sl2.
      clear.
      elim: l0 => //=.
      move => o l IH.
      by rewrite IH.
    have H_eq': sl1 = l1.
      rewrite /sl1 /pt_map_name_msg /tot_map_name /id /= /id /serialize_name_msg_tuple.
      clear.
      elim: l1 => //=.
      case => [n m] => /=.
      move => l IH.
      by rewrite serialize_deserialize_top_id IH.
    by rewrite H_eq H_eq'.
  - move => me src mg st out st' ps H_eq H_eq'.
    rewrite /net_handlers /= /serialized_net_handlers /= in H_eq'.
    rewrite /pt_map_msg /= in H_eq.
    move: H_eq H_eq'.
    case H_eq_m: (deserialize_top deserialize mg) => [mg'|] H_eq H_eq'; first by repeat break_let.
    by find_injection.
  - move => me inp st inp' H_eq.
    rewrite /pt_mapped_input_handlers.
    repeat break_let.
    rewrite /tot_map_name /= /id.
    rewrite /pt_map_input /= in H_eq.
    rewrite /input_handlers /= /serialized_input_handlers in Heqp.
    find_injection.
    rewrite /serialize_handler_result in Heqp.
    repeat break_let.
    find_injection.
    set sl2 := filterMap (fun _ => _) _.
    set sl1 := filterMap _ _.
    have H_eq: sl2 = l0.
      rewrite /sl2.
      clear.
      elim: l0 => //=.
      move => o l IH.
      by rewrite IH.
    have H_eq': sl1 = l1.
      rewrite /sl1 /pt_map_name_msg /tot_map_name /id /= /id /serialize_name_msg_tuple.
      clear.
      elim: l1 => //=.
      case => [n m] => /=.
      move => l IH.
      by rewrite serialize_deserialize_top_id IH.
    by rewrite H_eq H_eq'.
  - move => me inp st out st' ps H_eq H_eq'.
    rewrite /pt_map_msg /= in H_eq.
    by congruence.
  Qed.

  Lemma pt_map_net_deserialize_net : 
    forall net, pt_map_net net = deserialize_net net.
  Proof using.
  move => net.
  rewrite /deserialize_net.
  rewrite /pt_map_net /pt_map_data /= /id /= /pt_map_packet.
  set fm := filterMap _ _.
  set fm' := filterMap _ _.
  suff H_eq: fm = fm' by rewrite H_eq.
  rewrite /fm /fm'.
  clear.
  rewrite /pt_map_packet /tot_map_name /= /deserialize_packet.
  elim (nwPackets net) => //=.
  case => [src dst body] /= l IH.
  rewrite IH.
  by case (deserialize_top deserialize _).
  Qed.

  Lemma pt_map_onet_deserialize_onet : 
    forall net, pt_map_onet net = deserialize_onet net.
  Proof using. by []. Qed.
  
  Lemma pt_map_odnet_deserialize_odnet : 
    forall net, pt_map_odnet net = deserialize_odnet net.
  Proof using.
  move => net.
  rewrite /deserialize_odnet.
  rewrite /pt_map_odnet /pt_map_data /= /id /= /pt_map_msg.
  set fm := fun _ _ => filterMap _ _.
  rewrite map_id.
  set s := fun _ => match _ with _ => _ end.
  have H_eq: odnwState net = s.
    rewrite /s.
    apply functional_extensionality => n.
    by case: odnwState.
  by rewrite H_eq.
  Qed.

  Lemma step_async_deserialized_simulation :
  forall net net' tr,
    @step_async _ serialized_multi_params net net' tr ->
    @step_async _ orig_multi_params (deserialize_net net) (deserialize_net net') tr \/ 
    (deserialize_net net' = deserialize_net net).
  Proof using.
  move => net net' tr H_st.
  rewrite -2!pt_map_net_deserialize_net.
  have ->: tr = filterMap (@pt_map_trace_occ _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /pt_map_trace_occ /= /id.
    clear.
    elim: tr => //=.
    case => a; case => b l IH; first by rewrite -IH.
    rewrite -IH.
    set fm := filterMap _ _.
    have H_b: b = fm.
      rewrite /fm {fm}.
      elim: b => //=.
      move => o l' IH'.
      by rewrite -IH'.
    by rewrite H_b.
  apply step_async_pt_mapped_simulation_1 in H_st.
  case: H_st => H_st; first by left.
  break_and.
  by right.
  Qed.

  (* due to use of general simulation lemmas, this lemma is not as general as it could be *)
  (* if Cheerios-specific assumptions were used *)
  Lemma step_async_deserialized_simulation_star :
  forall net tr,
    @step_async_star _ serialized_multi_params step_async_init net tr ->
    exists tr', @step_async_star _ orig_multi_params step_async_init (deserialize_net net) tr' /\ 
     filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr'.
  Proof using.
  move => net tr H_st.
  apply step_async_pt_mapped_simulation_star_1 in H_st.
  break_exists.
  break_and.
  exists x.
  rewrite -pt_map_net_deserialize_net.
  split => //.
  find_reverse_rewrite.
  have <-: tr = filterMap (@pt_map_trace_occ _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /pt_map_trace_occ /= /id.
    clear.
    elim: tr => //=.
    case => a; case => b l IH; first by rewrite -IH.
    rewrite -IH.
    set fm := filterMap _ _.
    have H_b: b = fm.
      rewrite /fm {fm}.
      elim: b => //=.
      move => o l' IH'.
      by rewrite -IH'.
    by rewrite H_b.
  by [].
  Qed.

  Lemma step_failure_deserialized_simulation :
  forall net net' failed failed' tr,
    @step_failure _ _ serialized_failure_params (failed, net) (failed', net') tr ->
    @step_failure _ _ orig_failure_params (failed, deserialize_net net) (failed', deserialize_net net') tr \/ 
    (deserialize_net net' = deserialize_net net /\ failed = failed').
  Proof using.
  move => net net' failed failed' tr H_st.
  rewrite -2!pt_map_net_deserialize_net.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  have ->: tr = filterMap (@pt_map_trace_occ _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /pt_map_trace_occ /= /id.
    clear.
    elim: tr => //=.
    case => a; case => b l IH; first by rewrite -IH.
    rewrite -IH.
    set fm := filterMap _ _.
    have H_b: b = fm.
      rewrite /fm {fm}.
      elim: b => //=.
      move => o l' IH'.
      by rewrite -IH'.
    by rewrite H_b.
  apply step_failure_pt_mapped_simulation_1 in H_st.
  case: H_st => H_st; first by left.
  right.
  by break_and.  
  Qed.

  (* due to use of general simulation lemmas, this result is not as general as it could be *)
  (* if Cheerios-specific assumptions were used *)
  Lemma step_failure_deserialized_simulation_star :
  forall net failed tr,
    @step_failure_star _ _ serialized_failure_params step_failure_init (failed, net) tr ->
    exists tr', @step_failure_star _ _ orig_failure_params step_failure_init (failed, deserialize_net net) tr' /\ 
     filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr'.
  Proof using.
  move => net failed tr H_st.
  apply step_failure_pt_mapped_simulation_star_1 in H_st.
  break_exists.
  break_and.
  exists x.
  rewrite -pt_map_net_deserialize_net.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  split => //.
  rewrite -H0.
  have <-: tr = filterMap (@pt_map_trace_occ _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /pt_map_trace_occ /= /id.
    clear.
    elim: tr => //=.
    case => a; case => b l IH; first by rewrite -IH.
    rewrite -IH.
    set fm := filterMap _ _.
    have H_b: b = fm.
      rewrite /fm {fm}.
      elim: b => //=.
      move => o l' IH'.
      by rewrite -IH'.
    by rewrite H_b.
  by [].
  Qed.

  Lemma step_ordered_failure_deserialized_simulation :
    forall net net' failed failed' tr,
      @step_ordered_failure _ _ serialized_name_overlay_params serialized_fail_msg_params (failed, net) (failed', net') tr ->
      @step_ordered_failure _ _ orig_name_overlay_params orig_fail_msg_params (failed, deserialize_onet net) (failed', deserialize_onet net') tr \/
      deserialize_onet net = deserialize_onet net' /\ failed = failed' /\ tr = [].
  Proof using.
  move => net net' failed failed' tr H_st.
  eapply step_ordered_failure_pt_mapped_simulation_1 in H_st.
  case: H_st => H_st.
    have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n.
    have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n'.
    left.
    rewrite -2!pt_map_onet_deserialize_onet.
    have ->: tr = filterMap (@pt_map_trace_ev _ _ _ _ _ orig_multi_params_name_tot_map) tr.
      rewrite /pt_map_trace_ev /= /id.
      clear.
      elim: tr => //=.
      case => a; case => b l IH; first by rewrite -IH.
      by rewrite -IH.
    exact: H_st.
  right.
  break_and.
  split; first by rewrite -2!pt_map_onet_deserialize_onet.
  split => //.
  move: H1.
  rewrite /pt_map_trace_ev /= /id /=.
  set f := fun _ => _.
  clear.
  elim => //=.
  elim: tr => //=.
  case => n; case => /= [i|o] l IH.
  * by rewrite -IH.
  * by rewrite -IH.
  Qed.

  Lemma step_ordered_failure_serialized_simulation_star :
    forall net failed tr,
    @step_ordered_failure_star _ _ serialized_name_overlay_params serialized_fail_msg_params step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ orig_name_overlay_params orig_fail_msg_params step_ordered_failure_init (failed, deserialize_onet net) tr.
  Proof using.
  move => onet failed tr H_st.
  apply step_ordered_failure_pt_mapped_simulation_star_1 in H_st.
  rewrite -pt_map_onet_deserialize_onet.
  have ->: tr = filterMap (@pt_map_trace_ev _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /pt_map_trace_ev /= /id.
    clear.
    elim: tr => //=.
    case => a; case => b l IH; first by rewrite -IH.
    by rewrite -IH.
  by rewrite map_id in H_st.
  Qed.

  Lemma step_ordered_dynamic_failure_deserialized_simulation :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params (failed, deserialize_odnet net) (failed', deserialize_odnet net') tr \/
    deserialize_odnet net = deserialize_odnet net' /\ failed = failed' /\ tr = [].
  Proof using.
  move => net net' failed failed' tr H_nd H_st.
  eapply step_ordered_dynamic_failure_pt_mapped_simulation_1 in H_st; last by [].
  case: H_st => H_st.
    have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n.
    have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n'.
    left.
    rewrite -2!pt_map_odnet_deserialize_odnet.
    have ->: tr = filterMap (@pt_map_trace_ev _ _ _ _ _ orig_multi_params_name_tot_map) tr.
      rewrite /pt_map_trace_ev /= /id.
      clear.
      elim: tr => //=.
      case => a; case => b l IH; first by rewrite -IH.
      by rewrite -IH.
    exact: H_st.
  right.
  move: H_st => [H_eq_net [H_eq_f H_eq_tr]].
  split; first by rewrite -2!pt_map_odnet_deserialize_odnet.
  split => //.
  move: H_eq_tr.
  rewrite /pt_map_trace_ev /= /id.
  set f := fun _ => _.
  clear.
  elim => //=.
  elim: tr => //=.
  case => n; case => /= [i|o] l IH.
  * by rewrite -IH.
  * by rewrite -IH.
  Qed.

  Theorem step_ordered_dynamic_failure_deserialized_simulation_star :
    forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params step_ordered_dynamic_failure_init (failed, deserialize_odnet net) tr.
  Proof using.
  move => onet failed tr H_st.
  apply step_ordered_dynamic_failure_pt_mapped_simulation_star_1 in H_st.
  rewrite map_id in H_st.
  rewrite -pt_map_odnet_deserialize_odnet.
  have ->: tr = filterMap (@pt_map_trace_ev _ _ _ _ _ orig_multi_params_name_tot_map) tr.
    rewrite /pt_map_trace_ev /= /id.
    clear.
    elim: tr => //=.
    case => a; case => b l IH; first by rewrite -IH.
    by rewrite -IH.
  exact: H_st.
  Qed.
End SerializedMsgCorrect.
