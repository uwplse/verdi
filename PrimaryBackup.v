Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.
Require Import HandlerMonad.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Class PrimaryBackupParams (base_params : BaseParams) :=
  {
    input_eq_dec : forall x y : input, {x = y} + {x <> y}
  }.

Section PrimaryBackup.
  Context {base_params : BaseParams}.
  Context {one_node_params : OneNodeParams base_params}.
  Context {pb_params : PrimaryBackupParams base_params}.

  Inductive name := Primary | Backup.

  Lemma name_eq_dec : forall x y : name, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  Inductive msg :=
  | BackItUp : input -> msg
  | Ack : msg.

  Lemma msg_eq_dec : forall x y : msg, {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply input_eq_dec.
  Qed.

  Inductive PB_input :=
  | Request : input -> PB_input
  | Read : PB_input.

  Inductive PB_output :=
  | RequestResponse : input -> output -> PB_output
  | ReadResponse : data -> PB_output.

  Record PB_data :=
    {
      queue : list input;
      state : data
    }.

  Definition all_nodes : list name := [Primary; Backup].

  Lemma all_nodes_all :
    forall x,
      In x all_nodes.
  Proof.
    unfold all_nodes.
    destruct x; intuition.
  Qed.

  Lemma NoDup_all_nodes :
    NoDup all_nodes.
  Proof.
    unfold all_nodes.
    repeat constructor; intuition. simpl in *. intuition. congruence.
  Qed.

  Definition PB_init (n : name) :=
    Build_PB_data [] init.

  Definition set_queue {W O} (l : list input) :=
    modify (W := W)(O := O) (fun d => Build_PB_data l (state d)).

  Definition set_state {W O} (st : data) :=
    modify (W := W)(O := O) (fun d => Build_PB_data (queue d) st).

  Ltac pb_unfold := unfold set_queue, set_state in *; monad_unfold.

  Definition PB_input_handler (h : name) (i : PB_input) (d : PB_data) :
    list PB_output * PB_data * list (name * msg) :=
    runGenHandler_ignore d (
      match h, i with
        | Primary, Request r =>
          d <- get ;;
          when (null (queue d)) (send (Backup, BackItUp r)) ;;
          set_queue (queue d ++ [r])
        | _, Read =>
          d <- get ;;
          write_output (ReadResponse (state d))
        | _, _ => nop
      end).

  Lemma PB_input_handler_defn :
    forall h i d os d' ms,
      PB_input_handler h i d = (os, d', ms) ->
      (h = Primary /\
       state d' = state d /\
       os = [] /\
       exists r,
         i = Request r /\
         queue d' = queue d ++ [r] /\
         (ms = [] \/ (ms = [(Backup, BackItUp r)] /\ queue d = []))) \/
      (i = Read /\
       d = d' /\
       os = [ReadResponse (state d)] /\
       ms = []) \/
      (h = Backup /\
       d = d' /\
       ms = [] /\
       os = []).
  Proof.
    unfold PB_input_handler. intros.
    pb_unfold.
    repeat break_match; repeat find_inversion; intuition eauto.
    rewrite app_nil_r. simpl. find_apply_lem_hyp null_sound. find_rewrite.
    simpl. left. intuition. eexists. eauto.
  Qed.

  Definition PB_net (dst src : name) (m : msg) : PB_data ->
    list PB_output * PB_data * list (name * msg) :=
    fun x => runGenHandler_ignore x (
        match dst, m with
          | Primary, Ack => d <- get ;;
                            match queue d with
                              | [] => nop
                              | x :: xs => match xs with
                                             | [] => nop
                                             | y :: ys =>
                                               send (Backup, BackItUp y)
                                           end ;;
                                               let (os, st') := handler x (state d) in
                                               write_output (RequestResponse x os) ;;
                                               set_state st' ;;
                                               set_queue xs
                            end
          | Backup, BackItUp i => d <- get ;;
                                  set_state (snd (handler i (state d))) ;;
                                  send (Primary, Ack)
          | _, _ => nop
        end).

  Lemma PB_net_defn :
    forall dst src m d os d' ms,
      PB_net dst src m d = (os, d', ms) ->
      (os = [] /\ d' = d /\ ms = []) \/
      (dst = Primary /\ m = Ack /\ (
         (queue d = [] /\ os = [] /\ ms = [] /\ d' = d) \/
         (exists h t, queue d = h :: t /\
                      queue d' = t /\
                      ((t = [] /\ ms = []) \/
                       (exists y ys,
                          t = y :: ys /\
                          ms = [(Backup, BackItUp y)])) /\
                      let (us, st') := handler h (state d) in
                      os = [RequestResponse h us] /\
                      state d' = st'))) \/
      (dst = Backup /\ ms = [(Primary, Ack)] /\ queue d' = queue d /\ os = [] /\
       (exists i, m = BackItUp i /\
                  state d' = snd (handler i (state d)))).
  Proof.
    unfold PB_net. intros.
    pb_unfold. repeat (first [break_let | break_match]); repeat find_inversion; auto.
    - right. left. intuition. right. eexists. eexists. intuition eauto.
      find_rewrite. auto.
    - right. left. intuition. right. eexists. eexists. intuition eauto.
      find_rewrite. auto.
    - right. right. intuition. eexists. eauto.
  Qed.

  Lemma PB_net_defn' :
    forall dst src m d os d' ms,
      PB_net dst src m d = (os, d', ms) ->
      (os = [] /\ d' = d /\ ms = [] /\
       ((dst = Primary /\ exists i, m = BackItUp i) \/
        (dst = Backup /\ m = Ack))) \/
      (dst = Primary /\ m = Ack /\ (
         (queue d = [] /\ os = [] /\ ms = [] /\ d' = d) \/
         (exists h t, queue d = h :: t /\
                      queue d' = t /\
                      ((t = [] /\ ms = []) \/
                       (exists y ys,
                          t = y :: ys /\
                          ms = [(Backup, BackItUp y)])) /\
                      let (us, st') := handler h (state d) in
                      os = [RequestResponse h us] /\
                      state d' = st'))) \/
      (dst = Backup /\ ms = [(Primary, Ack)] /\ queue d' = queue d /\ os = [] /\
       (exists i, m = BackItUp i /\
                  state d' = snd (handler i (state d)))).
  Proof.
    unfold PB_net. intros.
    pb_unfold. repeat (first [break_let | break_match]); repeat find_inversion; auto; simpl.
    - left. intuition. left. eauto.
    - right. left. intuition.
    - right. left. intuition. right. eexists. eexists. intuition eauto.
      find_rewrite. auto.
    - right. left. intuition. right. eexists. eexists. intuition eauto.
      find_rewrite. auto.
    - right. right. intuition. eauto.
    - left. intuition.
  Qed.

  Instance PB_base_params : BaseParams :=
    Build_BaseParams
      PB_data
      PB_input
      PB_output.

  Instance PB_multi_params : MultiParams PB_base_params :=
    Build_MultiParams
      PB_base_params
      msg_eq_dec
      name_eq_dec
      all_nodes_all
      NoDup_all_nodes
      PB_init
      PB_net
      PB_input_handler.

  Definition inputs_1 (tr : list ((@input base_params) * (@output base_params))) :
      list (@input base_params) :=
    map (@fst _ _) tr.

  Definition inputs_m (tr : list (name * (@input PB_base_params + list (@output PB_base_params)))) :
    list (@input base_params) :=
    filterMap (fun x => match x with
                          | (Primary, inl (Request i)) => Some i
                          | _ => None
                        end)
              tr.

  Definition outputs_1 (tr : list ((@input base_params) * (@output base_params))) :
    list (@output base_params) :=
    map (@snd _ _) tr.

  Fixpoint outputs_m (tr : list (name * (@input PB_base_params + list (@output PB_base_params)))) :
    list (@output base_params) :=
    match tr with
      | [] => []
      | (Primary, inr l) :: tr' => filterMap (fun x => match x with
                                                         | RequestResponse i os => Some os
                                                         | _ => None
                                                       end) l ++ outputs_m tr'
      | _ :: tr' => outputs_m tr'
    end.

  Fixpoint processInputs (d : @data base_params) (l : list (@input base_params)) :
      (@data base_params * list (@output base_params)) :=
    match l with
      | [] => (d, [])
      | i :: l' => let (os, d') := @handler _ one_node_params i d in
                   let (d'', os') := processInputs d' l' in
                   (d'', os :: os')
    end.

  Definition correspond (st : @data base_params) (sigma : name -> @data PB_base_params) tr_1 tr_m :=
    let (d, os) := processInputs (state (sigma Primary)) (queue (sigma Primary)) in
    outputs_m tr_m ++ os = outputs_1 tr_1 /\
    d = st.

  Lemma inputs_1_nil_outputs_1_nil :
    forall tr,
      inputs_1 tr = [] ->
      outputs_1 tr = [].
  Proof.
    destruct tr; auto.
    intros. simpl in *. discriminate.
  Qed.

  Lemma inputs_m_app :
    forall l1 l2,
      inputs_m (l1 ++ l2) = inputs_m l1 ++ inputs_m l2.
  Proof.
    unfold inputs_m.
    intros.
    induction l1; simpl; repeat break_match; subst; simpl in *; auto using f_equal.
  Qed.

  Lemma inputs_m_inr :
    forall h t tr,
      inputs_m ((h, inr t) :: tr) = inputs_m tr.
  Proof.
    unfold inputs_m.
    intros.
    simpl.
    repeat break_match; auto; discriminate.
  Qed.

  Lemma PB_net_out_case :
    forall dst src m d os d' ms,
      PB_net dst src m d = (os, d', ms) ->
      (dst = Backup /\ os = [] /\ queue d' = queue d) \/
      (dst = Primary /\ os = [] /\ d' = d) \/
      (dst = Primary /\ exists h t, queue d = h :: t /\ queue d' = t /\
                                    (let (us, st') := handler h (state d) in
                                     os = [RequestResponse h us] /\ state d' = st')).
  Proof.
    intros.
    find_apply_lem_hyp PB_net_defn.
    intuition.
    - destruct dst; subst; intuition.
    - subst. right. right.
      intuition. break_exists. intuition eauto.
  Qed.

  Lemma outputs_m_app :
    forall tr1 tr2,
      outputs_m (tr1 ++ tr2) = outputs_m tr1 ++ outputs_m tr2.
  Proof.
    intros. induction tr1; simpl.
    - auto.
    - repeat break_match; subst; auto.
      rewrite app_ass. auto using f_equal.
  Qed.

  Lemma correspond_preserved_primary_same_no_outputs :
    forall sigma sigma' st tr_1 tr_m tr_m',
      correspond st sigma tr_1 tr_m ->
      sigma' Primary = sigma Primary ->
      outputs_m tr_m' = [] ->
      correspond st sigma' tr_1 (tr_m ++ tr_m').
  Proof.
    unfold correspond.
    intros.
    rewrite outputs_m_app.
    repeat find_rewrite.
    rewrite app_nil_r.
    auto.
  Qed.

  Lemma outputs_m_inr_nil :
    forall h l,
      outputs_m ((h,inr []) :: l) = outputs_m l.
  Proof.
    destruct h; auto.
  Qed.

  Lemma outputs_m_inr_nil_singleton :
    forall h,
      outputs_m [(h,inr [])] = [].
  Proof.
    intros.
    apply outputs_m_inr_nil.
  Qed.

  Lemma outputs_m_inl_read_singleton :
    forall h,
      outputs_m [(h, inl Read)] = [].
  Proof.
    destruct h; auto.
  Qed.

  Lemma outputs_m_inr_primary_singleton :
    forall h i l,
      h = Primary ->
      outputs_m [(h, inr [RequestResponse i l])] = [l].
  Proof.
    unfold outputs_m.
    intros.
    break_match; auto; congruence.
  Qed.

  Hint Extern 4 => congruence.

  Lemma correspond_preserved_primary_apply_entry :
    forall sigma sigma' st tr_1 tr_m tr_m' i l d h,
      correspond st sigma tr_1 tr_m ->
      handler i (state (sigma h)) = (l, state d) ->
      sigma' Primary = d ->
      outputs_m tr_m' = [l] ->
      h = Primary ->
      queue (sigma h) = i :: queue d ->
      correspond st sigma' tr_1 (tr_m ++ tr_m').
  Proof.
    unfold correspond.
    intros.
    subst.
    rewrite outputs_m_app.
    repeat find_rewrite.
    simpl in *.
    repeat break_match. repeat find_inversion.
    find_rewrite. find_inversion.
    rewrite app_ass. auto.
  Qed.

  Lemma inputs_m_inr_singleton :
    forall h l,
      inputs_m [(h, inr l)] = [].
  Proof.
    intros.
    rewrite inputs_m_inr.
    auto.
  Qed.

  Lemma inputs_m_app_inr_singleton :
    forall tr h l,
      inputs_m (tr ++ [(h, inr l)]) = inputs_m tr.
  Proof.
    intros.
    rewrite inputs_m_app in *.
    rewrite inputs_m_inr_singleton in *.
    rewrite app_nil_r in *.
    auto.
  Qed.

  Lemma inputs_m_primary_inl :
    forall i l,
      inputs_m ((Primary, inl (Request i)) :: l) = i :: inputs_m l.
  Proof.
    auto.
  Qed.

  Lemma inputs_m_primary_inl_request_singleton :
    forall i,
      inputs_m [(Primary, inl (Request i))] = [i].
  Proof.
    auto.
  Qed.

  Lemma inputs_m_inl_read_singleton :
    forall h,
      inputs_m [(h, inl Read)] = [].
  Proof.
    intros. destruct h; auto.
  Qed.

  Lemma inputs_m_inl_read :
    forall h l,
      inputs_m ((h, inl Read) :: l) = inputs_m l.
  Proof.
    intros. destruct h; auto.
  Qed.

  Lemma list_destruct_last :
    forall A (l : list A),
      l = [] \/ exists l' x, l = l' ++ [x].
  Proof.
    induction l; intuition.
    - subst. right. exists nil. simpl. eauto.
    - break_exists. subst. right. eexists. eexists.
      rewrite app_comm_cons. eauto.
  Qed.

  Lemma inputs_1_app :
    forall tr1 tr2,
      inputs_1 (tr1 ++ tr2) = inputs_1 tr1 ++ inputs_1 tr2.
  Proof.
    unfold inputs_1. auto using map_app.
  Qed.

  Lemma outputs_1_app :
    forall tr1 tr2,
      outputs_1 (tr1 ++ tr2) = outputs_1 tr1 ++ outputs_1 tr2.
  Proof.
    unfold outputs_1. auto using map_app.
  Qed.

  Lemma processInputs_app :
    forall l1 l2 d,
      processInputs d (l1 ++ l2) = let (d', os) := processInputs d l1 in
                                   let (d'', os') := processInputs d' l2 in
                                   (d'', os ++ os').
  Proof.
    induction l1; intros; simpl in *; repeat break_match.
    - auto.
    - find_inversion. find_higher_order_rewrite.
      repeat break_match. repeat find_inversion.
      repeat find_rewrite. find_inversion.
      auto.
  Qed.

  Lemma correspond_preserved_snoc :
    forall sigma tr_1 tr_m st sigma' st' i l,
      correspond st sigma tr_1 tr_m ->
      handler i st = (l, st') ->
      state (sigma' Primary) = state (sigma Primary) ->
      queue (sigma' Primary) = queue (sigma Primary) ++ [i] ->
      correspond st' sigma' (tr_1 ++ [(i,l)]) (tr_m ++ [(Primary, inl (Request i))]).
  Proof.
    unfold correspond.
    intros.
    rewrite outputs_m_app, outputs_1_app in *.
    repeat break_match.
    rewrite app_ass.
    simpl.
    repeat find_rewrite.
    rewrite processInputs_app in *.
    repeat break_match.
    repeat tuple_inversion.
    simpl in *. break_match. tuple_inversion.
    break_and. subst.
    find_rewrite. tuple_inversion.
    rewrite <- app_ass.
    find_rewrite.
    auto.
  Qed.

  Lemma inputs_m_backup_singleton :
    forall i,
      inputs_m [(Backup, inl i)] = [].
  Proof.
    auto.
  Qed.

  Lemma inputs_m_backup :
    forall i l,
      inputs_m ((Backup, inl i) :: l) = inputs_m l.
  Proof.
    auto.
  Qed.

  Lemma step_1_star_no_trace_no_step :
    forall st st' tr,
      step_1_star st st' tr ->
      tr = [] ->
      st = st'.
  Proof.
    intros.
    invc H; auto.
    invc H1. discriminate.
  Qed.

  Lemma inputs_1_nil_is_nil :
    forall tr,
      inputs_1 tr = nil ->
      tr = nil.
  Proof.
    intros.
    destruct tr; auto.
    discriminate.
  Qed.

  Lemma outputs_m_on_nil :
    outputs_m [] = [].
  Proof.
    auto.
  Qed.

  Lemma outputs_1_on_nil :
    outputs_1 (@nil ((@input base_params) * ((@output base_params)))) = [].
  Proof.
    auto.
  Qed.

  Lemma inputs_m_on_nil :
    inputs_m [] = [].
  Proof.
    auto.
  Qed.

  Lemma processInputs_cons_defn :
    forall (st : @data base_params) (x : @input base_params) l,
      processInputs st (x :: l) = let (os, d') := handler x st in
                                  let (d'', os') := processInputs d' l in
                                  (d'', os :: os').
  Proof.
    auto.
  Qed.

  Lemma processInputs_nil_defn :
    forall st,
      processInputs st [] = (st, []).
  Proof.
    auto.
  Qed.

  Lemma outputs_m_inl_singleton :
    forall h i,
      outputs_m [(h, inl i)] = [].
  Proof.
    destruct h; auto.
  Qed.

  Lemma inputs_1_singleton :
    forall l i,
      inputs_1 l = [i] ->
      exists os,
        l = [(i, os)].
  Proof.
    intros.
    destruct l; simpl in *.
    - discriminate.
    - find_inversion. find_apply_lem_hyp inputs_1_nil_is_nil. subst.
      destruct p. eauto.
  Qed.

  Lemma step_1_star_singleton_trace :
    forall st st' i os,
      step_1_star st st' [(i, os)] ->
      step_1 st st' [(i, os)].
  Proof.
    intros.
    invc H.
    invc H4.
    - rewrite app_nil_r in *. subst. auto.
    - invc H1. invc H. discriminate.
  Qed.

  Lemma step_1_singleton_inversion :
    forall st st' i os,
      step_1 st st' [(i, os)] ->
      handler i st = (os, st').
  Proof.
    intros.
    invc H.
    auto.
  Qed.

  Lemma inputs_m_on_nil' :
    inputs_m (@nil (name * (PB_input + (list PB_output)))) = [].
  Proof.
    unfold inputs_m. auto.
  Qed.

  Lemma correspond_init :
    correspond init PB_init [] [].
  Proof.
    unfold correspond.
    break_let.
    simpl in *. tuple_inversion. auto.
  Qed.

  Lemma inputs_1_invert_app :
    forall tr tr' x,
      inputs_1 tr = tr' ++ [x] ->
      exists y z,
        tr = y ++ [z] /\
        inputs_1 y = tr' /\
        inputs_1 [z] = [x].
  Proof.
    intros tr.
    pose proof list_destruct_last _ tr.
    intuition.
    - subst. destruct tr'; discriminate.
    - break_exists. subst.
      rewrite inputs_1_app in *.
      simpl in *.
      find_apply_lem_hyp app_inj_tail. intuition eauto.
  Qed.

  Lemma step_1_snoc_inv :
    forall st st' tr t,
      step_1_star st st' (tr ++ [t]) ->
      exists st2,
        step_1_star st st2 tr /\
        step_1 st2 st' [t].
  Proof.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    invc H.
    - destruct tr; discriminate.
    - invc H4. exists x'.
      find_apply_lem_hyp app_inj_tail.
      intuition. subst.
      + apply refl_trans_n1_1n_trace. auto.
      + subst. constructor. auto.
  Qed.

  Lemma outputs_m_read_response_singleton  :
    forall h o,
      outputs_m [(h, inr [ReadResponse o])] = [].
  Proof.
    intros.
    simpl in *.
    break_match; auto.
  Qed.

  Lemma correspond_reachable :
    forall net tr_m,
      step_m_star step_m_init net tr_m ->
      forall st tr_1,
        step_1_star init st tr_1 ->
        inputs_1 tr_1 = inputs_m tr_m ->
        correspond st (nwState net) tr_1 tr_m.
  Proof.
    intros net tr_m H.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H.
    induction H; intros; subst.
    - simpl in *. rewrite inputs_m_on_nil' in H3.
      destruct tr_1; try discriminate.
      invc H.
      + simpl. apply correspond_init.
      + invc H1. discriminate.
    - repeat concludes.
      invc H1; simpl in *.
      + find_apply_lem_hyp PB_net_defn.
        intuition; subst;
        try rewrite inputs_m_app in *;
        try rewrite inputs_m_inr_singleton in *;
        try rewrite app_nil_r in *;
        try break_exists;
        try break_let;
        try break_and;
        subst; repeat find_rewrite;
        eauto using
              correspond_preserved_primary_same_no_outputs,
        correspond_preserved_primary_apply_entry,
        update_nop,
        update_eq,
        update_diff,
        outputs_m_inr_nil_singleton.
      + find_apply_lem_hyp PB_input_handler_defn.
        intuition; subst;
        repeat rewrite snoc_assoc in *;
        repeat rewrite inputs_m_app in *.
        * break_exists. break_and. subst.
          rewrite inputs_m_inr_singleton in *. rewrite app_nil_r in *.
          rewrite inputs_m_primary_inl_request_singleton in *.
          find_apply_lem_hyp inputs_1_invert_app. break_exists. break_and.
          subst. simpl in *. find_inversion. destruct x1.
          find_apply_lem_hyp step_1_snoc_inv. break_exists. break_and.
          { eapply correspond_preserved_primary_same_no_outputs; eauto.
            eapply correspond_preserved_snoc; eauto.
            - eauto using step_1_singleton_inversion.
            - rewrite update_eq by auto. auto.
            - rewrite update_eq by auto. auto.
          }
        * rewrite inputs_m_inr_singleton in *. rewrite app_nil_r in *.
          rewrite inputs_m_inl_read_singleton in *. rewrite app_nil_r in *.
          eauto using
                correspond_preserved_primary_same_no_outputs,
          update_nop,
          outputs_m_inl_read_singleton,
          outputs_m_read_response_singleton.
        * rewrite inputs_m_inr_singleton in *.
          rewrite inputs_m_backup_singleton in *. repeat rewrite app_nil_r in *.
          eauto using correspond_preserved_primary_same_no_outputs, update_diff.
  Qed.

  Lemma correspond_inductive :
    forall net net' tr_m',
      step_m net net' tr_m' ->
      forall st st' tr_m tr_1 tr_1',
        correspond st (nwState net) tr_1 tr_m ->
        step_1_star st st' tr_1' ->
        inputs_1 tr_1' = inputs_m tr_m' ->
        correspond st' (nwState net') (tr_1 ++ tr_1') (tr_m ++ tr_m').
  Proof.
    intros.
    invc H; repeat break_let; simpl in *;
    repeat match goal with
          | [ H : context [ inputs_m [(_, inr _)] ] |- _ ] =>
            rewrite inputs_m_inr_singleton in H
          | [ H : context [ inputs_m [(Primary, inl (Request _))] ] |- _ ] =>
            rewrite inputs_m_primary_inl_request_singleton in H
          | [ H : context [ inputs_m ((Primary, inl (Request _)) :: _) ] |- _ ] =>
            rewrite inputs_m_primary_inl in H
          | [ H : context [ inputs_m [(_, inl Read)] ] |- _ ] =>
            rewrite inputs_m_inl_read_singleton in H
          | [ H : context [ inputs_m ((_, inl Read) :: _) ] |- _ ] =>
            rewrite inputs_m_inl_read in H
          | [ H : context [ inputs_1 _ = [] ] |- _ ] =>
            apply inputs_1_nil_is_nil in H; subst
          | [ H : context [ inputs_m [_] ] |- _ ] =>
            rewrite inputs_m_backup_singleton in H
          | [ H : context [ inputs_m (_ :: _) ] |- _ ] =>
            rewrite inputs_m_backup in H
          | [ H : step_1_star _ _ [] |- _ ] =>
            apply step_1_star_no_trace_no_step in H; [|solve [auto]]; subst
          | [ H : step_1_star _ _ [_] |- _ ] =>
            apply step_1_star_singleton_trace in H
          | [ H : step_1 _ _ [_] |- _ ] =>
            apply step_1_singleton_inversion in H
          | [ |- context [ _ ++ [] ] ] =>
            repeat rewrite app_nil_r
          | [ H : context [ _ ++ [] ] |- _ ] =>
            repeat rewrite app_nil_r in *
          | [ H : context [ [] ++ _ ] |- _ ] =>
            repeat rewrite app_nil_l in *
          | [ H : context [PB_net _ _ _ _] |- _ ] => apply PB_net_defn in H
          | [ H : context [PB_input_handler _ _ _] |- _ ] => apply PB_input_handler_defn in H
          | [ H : context [inputs_1 _ = [_]] |- _ ] => apply inputs_1_singleton in H

          | [ H : _ /\ _ |- _ ] => break_and
          | [ H : exists _, _ |- _ ] => break_exists
          | [ H : _ \/ _ |- _ ] => break_or_hyp
          | _ => repeat break_let; repeat find_rewrite; repeat tuple_inversion; subst; auto
        end; repeat rewrite snoc_assoc;
      eauto using
              correspond_preserved_primary_same_no_outputs,
              update_nop,
              update_diff,
              outputs_m_inr_nil_singleton,
              outputs_m_inl_read_singleton,
              outputs_m_read_response_singleton.
    - eapply correspond_preserved_primary_apply_entry; eauto using update_eq.
    - eapply correspond_preserved_primary_apply_entry; eauto using update_eq.
    - eapply correspond_preserved_primary_same_no_outputs; eauto.
      eapply correspond_preserved_snoc; eauto; rewrite update_eq by auto; repeat find_rewrite; auto.
    - eapply correspond_preserved_primary_same_no_outputs; eauto.
      eapply correspond_preserved_snoc; eauto; rewrite update_eq by auto; repeat find_rewrite; auto.
  Qed.

  Lemma step_m_outputs_m :
    forall net net' tr,
      step_m net net' tr ->
      (inputs_m tr = [] /\ (outputs_m tr = [] /\ nwState net Primary = nwState net' Primary)) \/
      (inputs_m tr = [] /\ exists os, outputs_m tr = [os]) \/
      (exists i, inputs_m tr = [i]).
  Proof.
    intros.
    invc H; simpl; break_match; auto;
    repeat rewrite app_nil_r in *;
    simpl in *;
    try find_apply_lem_hyp PB_net_defn;
    try find_apply_lem_hyp PB_input_handler_defn;
    intuition; subst.
    - rewrite inputs_m_inr_singleton.
      rewrite update_eq by auto.
      auto.
    - rewrite inputs_m_inr_singleton.
      rewrite update_eq by auto.
      auto.
    - break_exists. intuition; break_match.
      + intuition. subst.
        rewrite inputs_m_inr_singleton. simpl. eauto.
      + break_exists.  intuition. subst.
        rewrite inputs_m_inr_singleton. simpl. eauto.
    - rewrite inputs_m_inr_singleton.
      rewrite update_diff by auto. auto.
    - rewrite inputs_m_inr_singleton.
      rewrite update_diff by auto. auto.
    - break_exists. intuition; subst; rewrite inputs_m_primary_inl; eauto.
    - rewrite inputs_m_inl_read. rewrite update_eq by auto. auto.
    - rewrite inputs_m_inl_read. rewrite update_diff by auto. auto.
    - rewrite inputs_m_backup.
      rewrite update_diff by auto. auto.
  Qed.

  Definition network_invariant (net : @network _ PB_multi_params) : Prop :=
    (nwPackets net = [] /\ state (nwState net Primary) = state (nwState net Backup)) \/
    (exists i is, nwPackets net = [mkPacket Primary Backup (BackItUp i)] /\
               queue (nwState net Primary) = i :: is /\
               state (nwState net Primary) = state (nwState net Backup)) \/
    (nwPackets net = [mkPacket Backup Primary Ack] /\
     exists i is, queue (nwState net Primary) = i :: is /\
                  snd (handler i (state (nwState net Primary))) = state (nwState net Backup)).

  Ltac prep := subst; simpl in *; try find_inversion; repeat find_rewrite; simpl in *.

  Ltac workhorse :=
    repeat (prep;
            match goal with
             | [ H : _ /\ _ |- _ ] => break_and
             | [ H : exists _, _ |- _ ] => break_exists
             | [ H : _ ++ _ :: _ = [] |- _ ] => solve [exfalso; eapply app_cons_not_nil; eauto]
             | [ H : _ ++ _ :: _ = [ _ ] |- _ ] => apply app_cons_singleton_inv in H
             | [ H : context [ let (_,_) := ?X in _ ] |- _ ] => destruct X eqn:?
             | [ |- context [ let (_,_) := ?X in _ ] ] => destruct X eqn:?
             | [ |- context [ update (nwState ?net) ?x (nwState ?net ?x) _ ] ] => rewrite update_nop
             | [ |- context [ update _ ?x _ ?x ] ] => rewrite update_eq by auto
             | [ |- context [ update _ ?x _ ?y ] ] => rewrite update_diff by auto

             | [ H : _ \/ _ |- _ ] => invc H
           end); prep.

  Lemma network_invariant_inductive :
    forall net net' tr,
      step_m net net' tr ->
      network_invariant net ->
      network_invariant net'.
  Proof.
    intros.
    invc H; simpl in *.
    - unfold network_invariant in *. simpl.
      find_apply_lem_hyp PB_net_defn'.
      workhorse; auto; intuition eauto.
    - unfold network_invariant in *. simpl.
      find_apply_lem_hyp PB_input_handler_defn.
      workhorse; auto; intuition eauto.
  Qed.

  Lemma network_invariant_init :
    network_invariant step_m_init.
  Proof.
    unfold network_invariant. simpl. auto.
  Qed.

  Lemma correspond_Prefix :
    forall st net tr_1 tr_m,
      correspond st (nwState net) tr_1 tr_m ->
      Prefix (outputs_m tr_m) (outputs_1 tr_1).
  Proof.
    unfold correspond.
    intros. break_let. intuition. subst.
    eauto using app_Prefix.
  Qed.

  Fixpoint revert_trace (tr : list (name * ((@input PB_base_params) + list (@output PB_base_params)))) :
    list (@input base_params * (@output base_params)) :=
    match tr with
      | [] => []
      | (h, t) :: tr' => match t with
                           | inr l => filterMap (fun x => match x with
                                                            | RequestResponse i os => Some (i, os)
                                                            | _ => None
                                                          end) l
                           | _ => []
                         end ++ revert_trace tr'
    end.

  Definition revert_state (net : network) : @data base_params := state (nwState net Primary).

  Lemma revert_state_defn :
    forall net,
      revert_state net = state (nwState net Primary).
  Proof.
    unfold revert_state. auto.
  Qed.

  Lemma inductive_simulation :
    forall net net' tr,
      step_m net net' tr ->
      step_1_star (revert_state net) (revert_state net') (revert_trace tr).
  Proof.
    intros.
    invc H.
    - repeat rewrite revert_state_defn. simpl. rewrite app_nil_r.
      simpl in *.
      find_apply_lem_hyp PB_net_defn.
      intuition; subst.
      + rewrite update_nop. constructor.
      + rewrite update_nop. constructor.
      + break_exists. intuition; break_let.
        * intuition. subst.
          rewrite <- app_nil_r. econstructor; constructor. repeat find_rewrite.
          rewrite update_eq by auto. auto.
        * break_exists. intuition. subst. simpl in *.
          rewrite <- app_nil_r. econstructor; constructor. repeat find_rewrite.
          rewrite update_eq by auto. auto.
      + repeat find_rewrite.
        rewrite update_diff by auto. constructor.
    - repeat rewrite revert_state_defn. simpl in *.
      find_apply_lem_hyp PB_input_handler_defn.
      intuition; subst.
      + rewrite update_eq by auto. repeat find_rewrite. constructor.
      + rewrite update_nop. constructor.
      + rewrite update_diff by auto. constructor.
  Qed.

  Lemma revert_trace_app :
    forall tr1 tr2,
      revert_trace (tr1 ++ tr2) = revert_trace tr1 ++ revert_trace tr2.
  Proof.
    induction tr1; intros; simpl.
    - auto.
    - rewrite IHtr1.
      repeat break_match; subst.
      + auto.
      + rewrite app_ass. auto.
  Qed.

  Lemma simulation :
    forall net tr,
      step_m_star step_m_init net tr ->
      step_1_star init (revert_state net) (revert_trace tr).
  Proof.
    intros.
    apply refl_trans_1n_n1_trace in H.
    prep_induction H.
    induction H; intros; subst.
    - unfold step_m_init, revert_state. constructor.
    - repeat concludes. rewrite revert_trace_app.
      unfold step_1_star.
      find_apply_lem_hyp inductive_simulation.
      simpl in *.
      unfold step_1_star in *.
      eauto using refl_trans_1n_trace_trans.
  Qed.

  Theorem transformer :
    forall (P : list (input * output) -> Prop),
      (forall st tr,
         step_1_star init st tr ->
         P tr) ->
      (forall net tr,
         step_m_star step_m_init net tr ->
         P (revert_trace tr)).
  Proof.
    intros.
    find_apply_lem_hyp simulation.
    eauto.
  Qed.

  Lemma inputs_m_on_cons :
    forall t tr,
      inputs_m (t :: tr) = match t with
                             | (Primary, inl (Request i)) => i :: inputs_m tr
                             | _ => inputs_m tr
                           end.
  Proof.
    unfold inputs_m.
    intros. simpl.
    repeat break_match; repeat find_inversion; auto; try discriminate.
  Qed.

  Definition no_output_at_backup {A} x := forall y, snd x = @inr A _ y ->
                                                      fst x = Primary \/
                                                      match y with
                                                        | [] => True
                                                        | [ReadResponse _] => True
                                                        | _ => False
                                                      end.

  Definition no_output_at_backup_trace {A} tr := (forall x, In x tr -> @no_output_at_backup A x).

  Lemma NOABT_tail :
    forall A x y,
      @no_output_at_backup_trace A (x :: y) ->
      no_output_at_backup_trace y.
  Proof.
    unfold no_output_at_backup_trace.
    intros. simpl in *. eauto.
  Qed.

  Lemma NOABT_contra :
    forall A l tr,
      @no_output_at_backup_trace A ((Backup, inr l) :: tr) ->
      l = [] \/
      exists d,
        l = [ReadResponse d].
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    intros. simpl in *.
    find_insterU.
    econcludes.
    find_insterU.
    simpl in *.
    econcludes.
    intuition.
    repeat break_match; intuition eauto.
  Qed.

  Lemma outputs_m_revert_trace :
    forall tr,
      no_output_at_backup_trace tr ->
      outputs_m tr = outputs_1 (revert_trace tr).
  Proof.
    unfold outputs_1.
    induction tr; simpl; intros.
    - auto.
    - repeat break_match; subst.
      + eauto using NOABT_tail.
      + rewrite IHtr by eauto using NOABT_tail.
        rewrite map_app. rewrite map_of_filterMap.
        f_equal. apply filterMap_ext. intros.
        repeat break_match; auto.
      + rewrite IHtr by eauto using NOABT_tail. auto.
      + find_copy_apply_lem_hyp NOABT_tail.
        find_apply_lem_hyp NOABT_contra. intuition; break_exists;
        subst; simpl; auto.
  Qed.

  Lemma NOABT_nil :
    forall A,
      @no_output_at_backup_trace A [].
  Proof.
    unfold no_output_at_backup_trace.
    simpl. intuition.
  Qed.

  Lemma NOABT_cons :
    forall A x y,
      no_output_at_backup x ->
      @no_output_at_backup_trace A y ->
      no_output_at_backup_trace (x :: y).
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    simpl. intros. intuition; subst; eauto.
  Qed.

  Lemma NOABT_head :
    forall A x y,
      @no_output_at_backup_trace A (x :: y) ->
      no_output_at_backup x.
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    simpl. intuition.
  Qed.

  Lemma NOABT_app :
    forall A xs ys,
      @no_output_at_backup_trace A xs ->
      no_output_at_backup_trace ys ->
      no_output_at_backup_trace (xs ++ ys).
  Proof.
    induction xs; intros; simpl in *; auto.
    eauto using NOABT_cons,
    NOABT_head,
    NOABT_tail.
  Qed.

  Lemma NOABT_singleton_inr_nil :
    forall A h,
      @no_output_at_backup_trace A [(h, inr [])].
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    simpl. intros. intuition. subst. simpl in *. find_inversion. auto.
  Qed.

  Lemma NOABT_singleton_inr_read_response :
    forall A h d,
      @no_output_at_backup_trace A [(h, inr [ReadResponse d])].
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    simpl. intros. intuition. subst. simpl in *. find_inversion. auto.
  Qed.

  Lemma NOABT_singleton_primary :
    forall A out,
      no_output_at_backup_trace [(Primary, @inr A _ out)].
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    simpl.
    intuition.  subst. simpl in *. find_inversion. auto.
  Qed.

  Lemma NOABT_singleton_inl :
    forall A h r,
      @no_output_at_backup_trace A [(h, inl r)].
  Proof.
    unfold no_output_at_backup_trace, no_output_at_backup.
    simpl. intuition. subst. simpl in *. discriminate.
  Qed.

  Theorem pbj_NOABT :
    forall net tr,
      step_m_star (params:=PB_multi_params) step_m_init net tr ->
      no_output_at_backup_trace tr.
  Proof.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H.
    induction H; intros.
    - auto using NOABT_nil.
    - subst. repeat concludes.
      apply NOABT_app; auto.
      invc H1; simpl in *.
      + find_apply_lem_hyp PB_net_defn'.
        intuition; subst; repeat find_rewrite;
        auto using NOABT_singleton_inr_nil, NOABT_singleton_primary.
      + rewrite cons_cons_app. apply NOABT_app.
        * auto using NOABT_singleton_inl.
        * find_apply_lem_hyp PB_input_handler_defn.
          intuition; break_exists; intuition; subst;
          auto using NOABT_singleton_inr_nil, NOABT_singleton_inr_read_response.
  Qed.

  Definition zero_or_one_outputs_per_step {A B C} t :=
    forall y, @snd A _  t = @inr B _ y -> y = [] \/ exists z : C, y = [z].

  Definition zero_or_one_outputs_per_step_trace {A B C} tr :=
    forall x, In x tr -> @zero_or_one_outputs_per_step A B C x.

  Lemma ZOOOPST_nil :
    forall A B C,
      @zero_or_one_outputs_per_step_trace A B C [].
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl. intuition.
  Qed.

  Lemma ZOOOPST_head :
    forall A B C x y,
      @zero_or_one_outputs_per_step_trace A B C (x :: y) ->
      zero_or_one_outputs_per_step x.
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl.
    eauto.
  Qed.

  Lemma ZOOOPST_tail :
    forall A B C x y,
      @zero_or_one_outputs_per_step_trace A B C (x :: y) ->
      zero_or_one_outputs_per_step_trace y.
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl.
    eauto.
  Qed.

  Lemma ZOOOPST_cons_elim :
    forall A B C x y,
      @zero_or_one_outputs_per_step_trace A B C (x :: y) ->
      zero_or_one_outputs_per_step x /\
      zero_or_one_outputs_per_step_trace y.
  Proof.
    intuition eauto using ZOOOPST_head, ZOOOPST_tail.
  Qed.

  Lemma ZOOOPST_cons_intro :
    forall A B C x y,
      @zero_or_one_outputs_per_step A B C x ->
      zero_or_one_outputs_per_step_trace y ->
      zero_or_one_outputs_per_step_trace (x :: y).
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl.
    intuition; subst; simpl in *; try discriminate; eauto.
  Qed.

  Lemma ZOOOPST_app :
    forall A B C xs ys,
      @zero_or_one_outputs_per_step_trace A B C xs ->
      zero_or_one_outputs_per_step_trace ys ->
      zero_or_one_outputs_per_step_trace (xs ++ ys).
  Proof.
    induction xs; intros.
    - auto.
    - eauto using ZOOOPST_cons_intro, ZOOOPST_head, ZOOOPST_tail.
  Qed.

  Lemma ZOOOPST_singleton_nil :
    forall A B C h,
      @zero_or_one_outputs_per_step_trace A B C [(h, inr [])].
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl in *.
    intuition. subst. simpl in *. find_inversion. auto.
  Qed.

  Lemma ZOOOPST_singleton_singleton :
    forall A B C h x,
      @zero_or_one_outputs_per_step_trace A B C [(h, inr [x])].
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl. intuition. subst. simpl in *. find_inversion. eauto.
  Qed.

  Lemma ZOOOPST_singleton_inl :
    forall A B C h i,
      @zero_or_one_outputs_per_step_trace A B C [(h, inl i)].
  Proof.
    unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
    simpl. intuition. subst. discriminate.
  Qed.

  Theorem pbj_0_or_1 :
    forall net tr,
      step_m_star (params:=PB_multi_params) step_m_init net tr ->
      zero_or_one_outputs_per_step_trace tr.
  Proof.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H.
    induction H; intros; subst.
    - auto using ZOOOPST_nil.
    - repeat concludes.
      apply ZOOOPST_app; auto.
      invc H1; simpl in *.
      + find_apply_lem_hyp PB_net_defn.
        intuition; subst; auto using ZOOOPST_singleton_nil.
        break_exists. break_and. break_match.
        intuition; subst; auto using ZOOOPST_singleton_singleton.
      + rewrite cons_cons_app.
        apply ZOOOPST_app.
        * auto using ZOOOPST_singleton_inl.
        * find_apply_lem_hyp PB_input_handler_defn; intuition; subst;
          auto using ZOOOPST_singleton_nil, ZOOOPST_singleton_singleton.
  Qed.

  Lemma inputs_1_m_revert :
    forall net tr,
      step_m_star (params := PB_multi_params) step_m_init net tr ->
      inputs_m tr = inputs_1 (revert_trace tr) ++ queue (nwState net Primary).
  Proof.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H.
    induction H; intros; subst.
    - simpl. auto.
    - repeat concludes.
      rewrite inputs_m_app.
      rewrite revert_trace_app.
      rewrite inputs_1_app.
      rewrite IHrefl_trans_n1_trace.
      repeat rewrite app_ass.
      f_equal.
      invc H1; simpl in *.
      + find_apply_lem_hyp PB_net_defn.
        intuition; subst; simpl in *; rewrite (inputs_m_inr_singleton);
        rewrite app_nil_r.
        * rewrite update_nop. auto.
        * repeat find_rewrite. rewrite update_nop. auto.
        * break_exists. break_let.
          { intuition; subst.
            - repeat find_rewrite. rewrite app_nil_r. simpl. rewrite update_eq by auto. auto.
            - break_exists. intuition. subst. repeat find_rewrite.
              simpl. rewrite update_eq by auto. auto.
          }
        * break_exists.  intuition. repeat find_rewrite. rewrite update_diff by auto. auto.
      + find_apply_lem_hyp PB_input_handler_defn.
        intuition; subst; simpl in *.
        * break_exists.
          intuition; subst;
          rewrite (inputs_m_primary_inl); rewrite update_eq; auto.
        * rewrite (inputs_m_inl_read).
          rewrite inputs_m_inr_singleton.
          rewrite app_nil_r. rewrite update_nop. auto.
        * rewrite (inputs_m_backup).
          rewrite inputs_m_inr_singleton.
          rewrite app_nil_r. rewrite update_nop. auto.
  Qed.
End PrimaryBackup.
