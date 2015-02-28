Require Import List.
Import ListNotations.

Require Import Util.
Require Import VerdiTactics.

Section Linearizability.
  Variable K : Type.
  Variable K_eq_dec : forall x y : K, {x = y} + {x <> y}.

  Inductive op : Type :=
  | I : K -> op
  | O : K -> op.

  Definition op_eq_dec :
    forall x y : op, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  Inductive IR : Type :=
  | IRI : K -> IR
  | IRO : K -> IR
  | IRU : K -> IR.

  Definition IR_eq_dec :
    forall x y : IR, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  (* Hypothesis trace_NoDup : NoDup trace. *)
  (* also maybe: no Us *)
  (* alse maybe: every O has corresponding I before it *)

  Definition acknowledged_op (k : K) (trace : list op) :=
    In (O k) trace.

  Definition acknowledged_op_dec (k : K) (tr : list op) : {acknowledged_op k tr} + {~acknowledged_op k tr} :=
    in_dec op_eq_dec (O k) tr.

  Inductive acknowledge_all_ops : list op ->  list IR -> Prop :=
  | AAO_nil : acknowledge_all_ops [] []
  | AAO_IU : forall k tr out,
               ~ acknowledged_op k tr ->
               acknowledge_all_ops tr out ->
               acknowledge_all_ops (I k :: tr) (IRI k :: IRU k :: out)
  | AAO_I_dorp : forall k tr out,
                   ~ acknowledged_op k tr ->
                   acknowledge_all_ops tr out ->
                   acknowledge_all_ops (I k :: tr) out
  | AAO_IO : forall k tr out,
               acknowledged_op k tr ->
               acknowledge_all_ops tr out ->
               acknowledge_all_ops (I k :: tr) (IRI k :: out)
  | AAO_O : forall k tr out,
              acknowledge_all_ops tr out ->
              acknowledge_all_ops (O k :: tr) (IRO k :: out).

  Lemma acknowledge_all_ops_was_in :
    forall l ir,
      acknowledge_all_ops l ir ->
      forall k,
        In (IRI k) ir ->
        In (I k) l.
  Proof.
    induction 1; intros; simpl in *; intuition (auto; congruence).
  Qed.

  Fixpoint acknowledge_all_ops_func (l : list op) (target : list IR) : list IR :=
    match l with
      | [] => []
      | x :: xs => match x with
                     | I k => if acknowledged_op_dec k xs
                              then IRI k :: acknowledge_all_ops_func xs target
                              else if in_dec IR_eq_dec (IRU k) target
                                   then IRI k :: IRU k :: acknowledge_all_ops_func xs target
                                   else acknowledge_all_ops_func xs target
                     | O k => IRO k :: acknowledge_all_ops_func xs target
                   end
    end.

  Hint Constructors acknowledge_all_ops.

  Lemma acknowledge_all_ops_func_defn :
    forall x l target,
      acknowledge_all_ops_func (x :: l) target =
      match x with
        | I k => if acknowledged_op_dec k l
                 then IRI k :: acknowledge_all_ops_func l target
                 else if in_dec IR_eq_dec (IRU k) target
                      then IRI k :: IRU k :: acknowledge_all_ops_func l target
                      else acknowledge_all_ops_func l target
        | O k => IRO k :: acknowledge_all_ops_func l target
      end.
  Proof.
    intros.
    unfold acknowledge_all_ops_func. repeat break_match; auto.
  Qed.

  Lemma acknowledge_all_ops_func_correct :
    forall l target,
      acknowledge_all_ops l (acknowledge_all_ops_func l target).
  Proof.
    induction l; intros; simpl; repeat break_match; subst; eauto.
  Qed.

  Lemma acknowledge_all_ops_func_target_ext :
    forall l t t',
      (forall k, In (IRU k) t -> In (IRU k) t') ->
      (forall k, In (IRU k) t' -> In (IRU k) t) ->
      acknowledge_all_ops_func l t = acknowledge_all_ops_func l t'.
  Proof.
    induction l; simpl in *; repeat break_match; subst; intuition eauto using f_equal.
    repeat break_match; eauto using f_equal; solve [exfalso; eauto].
  Qed.

  Definition good_move (x y : IR) : Prop :=
    (forall k k', ~ (x = IRO k /\ y = IRI k')) /\
    (forall k, ~ (x = IRI k /\ y = IRO k)) /\
    (forall k, ~ (x = IRI k /\ y = IRU k)).

  Inductive IR_equivalent : list IR -> list IR -> Prop :=
  | IR_equiv_nil : IR_equivalent [] []
  | IR_equiv_cons : forall x xs ys,
                   IR_equivalent xs ys ->
                   IR_equivalent (x :: xs) (x :: ys)
  | IR_equiv_move : forall x y xs ys,
                   IR_equivalent xs ys ->
                   good_move x y ->
                   IR_equivalent (x :: y :: xs) (y :: x :: ys)
  | IR_equiv_trans : forall l1 l2 l3,
                    IR_equivalent l1 l2 ->
                    IR_equivalent l2 l3 ->
                    IR_equivalent l1 l3.
  Hint Constructors IR_equivalent.

  Lemma IR_equivalent_refl :
    forall l,
      IR_equivalent l l.
  Proof.
    induction l; eauto.
  Qed.

  Lemma IR_equiv_in_l_r :
    forall ir1 ir2,
      IR_equivalent ir1 ir2 ->
      forall o,
        In o ir1 -> In o ir2.
  Proof.
    induction 1; intros; simpl in *; intuition.
  Qed.

  Lemma IR_equiv_in_r_l :
    forall ir1 ir2,
      IR_equivalent ir1 ir2 ->
      forall o,
        In o ir2 -> In o ir1.
  Proof.
    induction 1; intros; simpl in *; intuition.
  Qed.

  Require Import Permutation.
  Hint Constructors Permutation.
  Lemma IR_equiv_Permutation :
    forall ir1 ir2,
      IR_equivalent ir1 ir2 ->
      Permutation ir1 ir2.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma IR_equiv_app_head :
    forall l xs ys,
      IR_equivalent xs ys ->
      IR_equivalent (l ++ xs) (l ++ ys).
  Proof.
    induction l; intros; simpl; auto.
  Qed.

  Lemma IR_equiv_snoc :
    forall xs ys x,
      IR_equivalent xs ys ->
      IR_equivalent (xs ++ [x]) (ys ++ [x]).
  Proof.
    induction 1; simpl; eauto.
  Qed.

  Lemma IR_equiv_app_tail :
    forall l xs ys,
      IR_equivalent xs ys ->
      IR_equivalent (xs ++ l) (ys ++ l).
  Proof.
    induction 1; intros; simpl in *; eauto using IR_equivalent_refl.
  Qed.

  Section Examples.
    Example IR_equiv_eg1 :
      forall k k',
        k <> k' ->
        IR_equivalent [IRI k; IRI k'; IRO k; IRO k'] [IRI k; IRO k; IRI k'; IRO k'].
    Proof.
      intros.
      constructor.
      econstructor; auto.
      red.
      intuition (auto; congruence).
    Qed.

    Example IR_equiv_eg2 :
      forall k k',
        k <> k' ->
        IR_equivalent [IRI k; IRI k'; IRO k; IRO k'] [IRI k'; IRO k'; IRI k; IRO k].
    Proof.
      intros.
      eapply IR_equiv_trans with (l2 := [IRI k; IRI k'; IRO k'; IRO k]).
      - repeat constructor; unfold good_move; intuition (try congruence).
      - eapply IR_equiv_trans with (l2 := [IRI k'; IRI k; IRO k'; IRO k]).
        + apply IR_equiv_move; auto using IR_equivalent_refl.
          red. intuition congruence.
        + constructor. apply IR_equiv_move; auto.
          red. intuition congruence.
    Qed.

    Example IR_equiv_eg3 :
      forall k k',
        k <> k' ->
        IR_equivalent [IRI k; IRI k'; IRO k'; IRO k] [IRI k'; IRO k'; IRI k; IRO k].
    Proof.
      intros.
      eapply IR_equiv_trans with (l2 := [IRI k'; IRI k; IRO k'; IRO k]).
      - constructor.
        + apply IR_equivalent_refl.
        + red. intuition congruence.
      - constructor. constructor.
        + apply IR_equivalent_refl.
        + red. intuition congruence.
    Qed.

    Example IR_equiv_eg4 :
      forall k k',
        k <> k' ->
        IR_equivalent [IRI k; IRI k'; IRO k'; IRO k] [IRI k; IRO k; IRI k'; IRO k'].
    Proof.
      intros.
      constructor.
      eapply IR_equiv_trans with (l2 := [IRI k'; IRO k; IRO k']).
      - repeat constructor; unfold good_move; intuition congruence.
      - eapply IR_equiv_move; auto.
        red. intuition congruence.
    Qed.
  End Examples.

  Fixpoint good_trace (l : list IR) : Prop :=
    match l with
      | [] => True
      | IRI k :: IRO k' :: l' => k = k' /\ good_trace l'
      | IRI k :: IRU k' :: l' => k = k' /\ good_trace l'
      | _ => False
    end.

  Definition equivalent (l : list op) (ir : list IR) : Prop :=
    good_trace ir /\
    exists ir',
      acknowledge_all_ops l ir' /\
      IR_equivalent ir' ir.

  Lemma acknowledge_all_ops_func_IRU_In :
    forall l ir k,
      In (IRU k) (acknowledge_all_ops_func l ir) ->
      In (I k) l.
  Proof.
    induction l; intros; simpl in *; repeat break_match; subst; simpl in *;
    intuition (eauto; congruence).
  Qed.

  Definition get_op_input_keys (l : list op) : list K :=
    filterMap (fun x => match x with
                          | I k => Some k
                          | _ => None
                        end) l.

  Lemma get_op_input_keys_defn :
    forall x l,
      get_op_input_keys (x :: l) = match x with
                               | I k => k :: get_op_input_keys l
                               | _ => get_op_input_keys l
                                   end.
  Proof.
    unfold get_op_input_keys.
    intros.
    simpl. repeat break_match; congruence.
  Qed.

  Definition get_IR_input_keys (l : list IR) : list K :=
    filterMap (fun x => match x with
                          | IRI k => Some k
                          | _ => None
                        end) l.

  Lemma get_IR_input_keys_defn :
    forall x l,
      get_IR_input_keys (x :: l) = match x with
                               | IRI k => k :: get_IR_input_keys l
                               | _ => get_IR_input_keys l
                             end.
  Proof.
    unfold get_IR_input_keys.
    intros.
    simpl. repeat break_match; congruence.
  Qed.

  Definition get_op_output_keys (l : list op) : list K :=
    filterMap (fun x => match x with
                          | O k => Some k
                          | _ => None
                        end) l.

  Lemma get_op_output_keys_defn :
    forall x l,
      get_op_output_keys (x :: l) = match x with
                                      | O k => k :: get_op_output_keys l
                                      | _ => get_op_output_keys l
                                    end.
  Proof.
    unfold get_op_output_keys.
    intros.
    simpl.
    repeat break_match; congruence.
  Qed.

  Definition get_IR_output_keys (l : list IR) : list K :=
    filterMap (fun x => match x with
                          | IRO k => Some k
                          | IRU k => Some k
                          | _ => None
                        end) l.

  Lemma get_IR_output_keys_defn :
    forall x l,
      get_IR_output_keys (x :: l) = match x with
                                      | IRO k => k :: get_IR_output_keys l
                                      | IRU k => k :: get_IR_output_keys l
                                      | _ => get_IR_output_keys l
                                    end.
  Proof.
    unfold get_IR_output_keys.
    intros. simpl. repeat break_match; congruence.
  Qed.

  (* this is cleaner than the auto-generated functional induction scheme *)
  Fixpoint good_trace_ind'
    (P : list IR -> Prop -> Prop)
    (l : list IR) :
      P [] True ->
      (forall k, P [IRI k] False) ->
      (forall k k' l, P (IRI k :: IRI k' :: l) False) ->
      (forall k k' l, P l (good_trace l) -> P (IRI k :: IRO k' :: l) (k = k' /\ good_trace l)) ->
      (forall k k' l, P l (good_trace l) -> P (IRI k :: IRU k' :: l) (k = k' /\ good_trace l)) ->
      (forall k l, P (IRO k :: l) False) ->
      (forall k l, P (IRU k :: l) False) ->
      P l (good_trace l).
  Proof.
    intros.
    destruct l; simpl; repeat break_match; auto; subst.
    - match goal with
        | [ H : context [IRI _ :: IRO _ :: _ ] |- _ ] => apply H
      end.
      apply good_trace_ind'; auto.
    - match goal with
        | [ H : context [IRI _ :: IRU _ :: _ ] |- _ ] => apply H
      end.
      apply good_trace_ind'; auto.
  Qed.

  Lemma good_trace_ind :
    forall P : list IR -> Prop -> Prop,
      P [] True ->
      (forall k, P [IRI k] False) ->
      (forall k k' ir, P (IRI k :: IRI k' :: ir) False) ->
      (forall k k' ir, P ir (good_trace ir) -> P (IRI k :: IRO k' :: ir) (k = k' /\ good_trace ir)) ->
      (forall k k' ir, P ir (good_trace ir) -> P (IRI k :: IRU k' :: ir) (k = k' /\ good_trace ir)) ->
      (forall k ir, P (IRO k :: ir) False) ->
      (forall k ir, P (IRU k :: ir) False) ->
      forall ir, P ir (good_trace ir).
  Proof.
    intros.
    apply good_trace_ind'; auto.
  Qed.

  Lemma good_trace_IRI_in :
    forall ir,
      good_trace ir ->
      forall k,
        In (IRI k) ir ->
        In (IRO k) ir \/ In (IRU k) ir.
  Proof.
    intros ir.
    induction ir, good_trace using good_trace_ind; intros; simpl in *; intuition (auto; try congruence).
    - subst. find_apply_hyp_hyp. intuition.
    - subst. find_apply_hyp_hyp. intuition.
  Qed.

  Lemma acknowledge_all_ops_func_target_nil :
    forall l,
      (forall k, ~ In (O k) l) ->
      acknowledge_all_ops_func l [] = [].
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat break_match; subst; unfold acknowledged_op in *;
      (exfalso + idtac); solve [intuition eauto].
  Qed.

  Lemma before_head_op :
    forall l h ir,
      (forall k1 k2,
         In (I k2) l ->
         before (O k1) (I k2) l ->
         before (IRO k1) (IRI k2) (IRI h :: ir)) ->
      forall x,
        In (I h) l ->
        before x (I h) l ->
        exists k,
          x = I k.
  Proof.
    intros. destruct x. eauto.
    eapply_prop_hyp In In; eauto.
    simpl in *. intuition congruence.
  Qed.

  Lemma good_move_II :
    forall k k',
      good_move (IRI k) (IRI k').
  Proof.
    red. intuition congruence.
  Qed.

  Lemma good_move_OO :
    forall k k',
      good_move (IRO k) (IRO k').
  Proof.
    red. intuition congruence.
  Qed.

  Lemma IR_equivalent_all_Is_I :
    forall l k,
      (forall x, In x l -> exists k, x = IRI k) ->
      IR_equivalent (l ++ [IRI k]) (IRI k :: l).
  Proof.
    induction l; intros; simpl in *; intuition.
    apply IR_equiv_trans with (l2 := (a :: IRI k :: l)).
    - auto.
    - specialize (H a). concludes. break_exists. subst.
      auto using IR_equivalent_refl, good_move_II.
  Qed.

  Definition good_op_move (x y : op) : Prop :=
    (forall k k', ~ (x = O k /\ y = I k')) /\
    (forall k, ~ (x = I k /\ y = O k)).

  Inductive op_equivalent : list op -> list op -> Prop :=
  | op_equiv_nil : op_equivalent [] []
  | op_equiv_cons : forall x xs ys, op_equivalent xs ys -> op_equivalent (x :: xs) (x :: ys)
  | op_equiv_move : forall x y xs ys, good_op_move x y ->
                                      op_equivalent xs ys -> op_equivalent (x :: y :: xs) (y :: x :: ys)
  | op_equiv_trans : forall l1 l2 l3, op_equivalent l1 l2 -> op_equivalent l2 l3 -> op_equivalent l1 l3.

  Lemma op_equiv_Permutation :
    forall xs ys,
      op_equivalent xs ys ->
      Permutation xs ys.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma op_equiv_ack_op_lr :
    forall xs ys,
      op_equivalent xs ys ->
      forall k,
        acknowledged_op k xs ->
        acknowledged_op k ys.
  Proof.
    unfold acknowledged_op.
    intros.
    eauto using Permutation_in, op_equiv_Permutation.
  Qed.

  Lemma op_equiv_ack_op_rl :
    forall xs ys,
      op_equivalent xs ys ->
      forall k,
        acknowledged_op k ys ->
        acknowledged_op k xs.
  Proof.
    unfold acknowledged_op.
    intros.
    eauto using Permutation_sym, Permutation_in, op_equiv_Permutation.
  Qed.

  Lemma acknowledged_op_defn :
    forall k xs,
      acknowledged_op k xs ->
      In (O k) xs.
  Proof.
    auto.
  Qed.

  Lemma good_move_U_l :
    forall k x,
      good_move (IRU k) x.
  Proof.
    red. intuition congruence.
  Qed.

  Lemma good_move_IU_neq :
    forall k k',
      k <> k' ->
      good_move (IRI k) (IRU k').
  Proof.
    red. intuition congruence.
  Qed.

  Lemma good_move_IO_neq :
    forall k k',
      k <> k' ->
      good_move (IRI k) (IRO k').
  Proof.
    red. intuition congruence.
  Qed.

  Hint Resolve IR_equivalent_refl.
  Hint Resolve good_move_II.
  Hint Resolve good_move_U_l.

  Lemma not_good_op_move_IO :
    forall k,
      good_op_move (I k) (O k) -> False.
  Proof.
    unfold good_op_move.
    intuition eauto.
  Qed.

  Lemma not_good_op_move_OI :
    forall k k',
      good_op_move (O k) (I k') -> False.
  Proof.
    unfold good_op_move.
    intuition eauto.
  Qed.

  Lemma good_op_move_good_move_IO :
    forall k k',
      good_op_move (I k) (O k') ->
      good_move (IRI k) (IRO k').
  Proof.
    unfold good_op_move, good_move.
    intuition (try congruence). repeat find_inversion. eauto.
  Qed.

  Lemma good_op_move_cases :
    forall x y,
      good_op_move x y ->
      exists k k',
        (x = I k /\ y = I k') \/
        (x = O k /\ y = O k') \/
        (k <> k' /\ x = I k /\ y = O k').
  Proof.
    unfold good_op_move. intros.
    destruct x as [k|k], y as [k'|k']; exists k, k'; intuition.
    - right. right. intuition. subst. eauto.
    - exfalso. eauto.
  Qed.

  Lemma acknowledged_op_I_cons_reduce :
    forall k k' l,
      acknowledged_op k (I k' :: l) ->
      acknowledged_op k l.
  Proof.
    unfold acknowledged_op.
    simpl. intuition congruence.
  Qed.

  Lemma acknowledged_op_I_cons_expand :
    forall k k' l,
      acknowledged_op k l ->
      acknowledged_op k (I k' :: l).
  Proof.
    unfold acknowledged_op.
    simpl. intuition congruence.
  Qed.

  Hint Constructors op_equivalent.

  Lemma IR_equiv_AAOF_I :
    forall k xs ys target,
      op_equivalent xs ys ->
      IR_equivalent (acknowledge_all_ops_func xs target)
                    (acknowledge_all_ops_func ys target) ->
      IR_equivalent (acknowledge_all_ops_func (I k :: xs) target)
                    (acknowledge_all_ops_func (I k :: ys) target).
  Proof.
    intros.
    simpl.
    repeat break_match; auto;
    exfalso; eauto using op_equiv_ack_op_lr, op_equiv_ack_op_rl.
  Qed.

  Lemma IR_equiv_AAOF_II_neq :
    forall xs ys target k k',
      k <> k' ->
      op_equivalent xs ys ->
      IR_equivalent (acknowledge_all_ops_func xs target)
                    (acknowledge_all_ops_func ys target) ->
      IR_equivalent (acknowledge_all_ops_func (I k :: I k' :: xs) target)
                    (acknowledge_all_ops_func (I k' :: I k :: ys) target).
  Proof.
    intros.
    rewrite acknowledge_all_ops_func_defn.
    break_if.
    - rewrite acknowledge_all_ops_func_defn.
      break_if; rewrite acknowledge_all_ops_func_defn with (l := _ :: _).
      + rewrite if_decider_true by
                  eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr,
                              acknowledged_op_I_cons_reduce.
        rewrite acknowledge_all_ops_func_defn.
        rewrite if_decider_true by
            eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr,
                        acknowledged_op_I_cons_reduce.
        auto.
      + rewrite if_decider_false with (dec := acknowledged_op_dec _) by
        intuition eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
                              acknowledged_op_I_cons_reduce.
        rewrite acknowledge_all_ops_func_defn.
        rewrite if_decider_true with (dec := acknowledged_op_dec _) by
            eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr,
                              acknowledged_op_I_cons_reduce.
        break_if.
        * eauto 6 using good_move_IU_neq.
        * auto.
    - break_if; rewrite acknowledge_all_ops_func_defn.
      + break_if; rewrite acknowledge_all_ops_func_defn.
        * rewrite if_decider_true by
              eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr,
                            acknowledged_op_I_cons_reduce.
          rewrite acknowledge_all_ops_func_defn.
          rewrite if_decider_false by
              intuition eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
                            acknowledged_op_I_cons_reduce.
          rewrite if_decider_true by auto.
          eauto.
        * rewrite if_decider_false with (dec := acknowledged_op_dec _) by
              eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
              acknowledged_op_I_cons_reduce.
          rewrite acknowledge_all_ops_func_defn.
          rewrite if_decider_false with (dec := acknowledged_op_dec _) by
              eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
              acknowledged_op_I_cons_reduce.
          rewrite if_decider_true with (dec := in_dec _ (IRU k)) by auto.
          { break_if.
            - eapply IR_equiv_trans; [apply IR_equiv_cons; apply IR_equiv_move; auto|].
              eapply IR_equiv_trans; [apply IR_equiv_move; auto|]. constructor.
              eapply IR_equiv_trans; [apply IR_equiv_cons; apply IR_equiv_move; auto|].
              auto using good_move_IU_neq.
            - auto.
          }
      + break_if; rewrite acknowledge_all_ops_func_defn.
        * rewrite if_decider_true with (dec := acknowledged_op_dec _) by
              eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr,
                  acknowledged_op_I_cons_reduce.
          rewrite acknowledge_all_ops_func_defn.
          rewrite if_decider_false with (dec := acknowledged_op_dec _) by
              eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
                  acknowledged_op_I_cons_reduce.
          rewrite if_decider_false by auto.
          auto.
        * rewrite if_decider_false with (dec := acknowledged_op_dec _) by
              eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
                  acknowledged_op_I_cons_reduce.
           rewrite acknowledge_all_ops_func_defn.
           rewrite if_decider_false with (dec := acknowledged_op_dec _) by
              eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl,
                  acknowledged_op_I_cons_reduce.
           rewrite if_decider_false with (dec := in_dec _ (IRU k)) by auto.
           break_if; auto.
  Qed.

  Lemma op_equiv_AAOF_IR_equiv :
    forall xs ys,
      op_equivalent xs ys ->
      forall l,
        IR_equivalent (acknowledge_all_ops_func xs l) (acknowledge_all_ops_func ys l).
  Proof.
    induction 1; intros.
    - auto.
    - simpl.
      repeat break_match; subst; auto;
      exfalso; eauto using op_equiv_ack_op_lr, op_equiv_ack_op_rl.
    - find_copy_apply_lem_hyp good_op_move_cases. break_exists. intuition; subst.
      + destruct (K_eq_dec x0 x1).
        * subst. auto using IR_equiv_AAOF_I.
        * auto using IR_equiv_AAOF_II_neq.
      + simpl. eauto using good_move_OO.
      + simpl. repeat break_match; intuition; try congruence.
        * eauto using good_move_IO_neq.
        * exfalso. eauto using op_equiv_ack_op_lr.
        * exfalso. eauto using op_equiv_ack_op_lr.
        * exfalso; eauto using Permutation_in, op_equiv_Permutation, acknowledged_op_defn, Permutation_sym.
        * eapply IR_equiv_trans; [apply IR_equiv_cons; apply IR_equiv_move; auto|].
          eapply IR_equiv_trans; [apply IR_equiv_move; auto|]. apply good_move_IO_neq. congruence.
          auto.
        * exfalso.
          match goal with
            | [ H : In (O _) _ -> False |- _ ] => apply H
          end.
          eapply Permutation_in; [apply Permutation_sym; eapply op_equiv_Permutation; eauto|].
          auto using acknowledged_op_defn.
    - eauto.
  Qed.

  Lemma op_equivalent_refl :
    forall xs,
      op_equivalent xs xs.
  Proof.
    induction xs; auto.
  Qed.

  Lemma good_op_move_II :
    forall k k',
      good_op_move (I k) (I k').
  Proof.
    red. intuition congruence.
  Qed.

  Lemma op_equivalent_all_Is_I :
    forall l k,
      (forall x, In x l -> exists k, x = I k) ->
      op_equivalent (l ++ [I k]) (I k :: l).
  Proof.
    induction l; intros; simpl in *; intuition.
    apply op_equiv_trans with (l2 := (a :: I k :: l)).
    - auto.
    - specialize (H a). concludes. break_exists. subst.
      auto using op_equivalent_refl, good_op_move_II.
  Qed.

  Lemma good_op_move_neq_IO :
    forall k k',
      k <> k' ->
      good_op_move (I k) (O k').
  Proof.
    unfold good_op_move.
    intuition congruence.
  Qed.

  Lemma good_op_move_OO :
    forall k k',
      good_op_move (O k) (O k').
  Proof.
    unfold good_op_move.
    intuition congruence.
  Qed.

  Lemma op_equivalent_all_Is_O :
    forall l k,
      (forall k', In (I k') l -> k <> k') ->
      op_equivalent (l ++ [O k]) (O k :: l).
  Proof.
    induction l; intros; simpl in *; intuition.
    apply op_equiv_trans with (l2 := (a :: O k :: l)).
    - eauto 10.
    - destruct a.
      + eauto 6 using good_op_move_neq_IO, op_equivalent_refl.
      + eauto 6 using good_op_move_OO, op_equivalent_refl.
  Qed.

  Lemma op_equiv_app_tail :
    forall l xs ys,
      op_equivalent xs ys ->
      op_equivalent (xs ++ l) (ys ++ l).
  Proof.
    induction 1; intros; simpl in *; intuition.
    - auto using op_equivalent_refl.
    - eauto.
  Qed.

  Lemma op_equivalent_all_Is_I_middle :
    forall xs ys k,
      (forall x, In x xs -> exists k, x = I k) ->
      op_equivalent (xs ++ I k :: ys) (I k :: xs ++ ys).
  Proof.
    intros.
    rewrite app_comm_cons.
    replace (xs ++ I k :: ys) with ((xs ++ [I k]) ++ ys) by now rewrite app_ass.
    auto using op_equiv_app_tail, op_equivalent_all_Is_I.
  Qed.

  Lemma get_op_input_keys_app :
    forall xs ys,
      get_op_input_keys (xs ++ ys) = get_op_input_keys xs ++ get_op_input_keys ys.
  Proof.
    intros.
    apply filterMap_app.
  Qed.

  Lemma get_op_output_keys_app :
    forall xs ys,
      get_op_output_keys (xs ++ ys) = get_op_output_keys xs ++ get_op_output_keys ys.
  Proof.
    intros.
    apply filterMap_app.
  Qed.

  Lemma get_op_input_keys_complete :
    forall xs k,
      In (I k) xs ->
      In k (get_op_input_keys xs).
  Proof.
    unfold get_op_input_keys.
    intros.
    eapply filterMap_In; eauto.
    auto.
  Qed.

  Lemma get_op_input_keys_sound :
    forall k l,
      In k (get_op_input_keys l) ->
      In (I k) l.
  Proof.
    induction l; intros.
    - auto.
    - simpl in *. rewrite get_op_input_keys_defn in *. break_match; simpl in *.
      + subst. intuition congruence.
      + intuition.
  Qed.

  Lemma get_op_input_keys_preserves_NoDup :
    forall l,
      NoDup l ->
      NoDup (get_op_input_keys l).
  Proof.
    intros.
    unfold get_op_input_keys.
    apply filterMap_NoDup_inj; auto.
    intros.
    repeat break_match; try discriminate.
    subst. congruence.
  Qed.

  Lemma get_op_output_keys_complete :
    forall xs k,
      In (O k) xs ->
      In k (get_op_output_keys xs).
  Proof.
    unfold get_op_input_keys.
    intros.
    eapply filterMap_In; eauto.
    auto.
  Qed.

  Lemma get_IR_output_keys_complete_U :
    forall xs k,
      In (IRU k) xs ->
      In k (get_IR_output_keys xs).
  Proof.
    unfold get_IR_output_keys.
    intros.
    eapply filterMap_In; eauto. auto.
  Qed.

  Lemma get_IR_output_keys_complete_O :
    forall xs k,
      In (IRO k) xs ->
      In k (get_IR_output_keys xs).
  Proof.
    unfold get_IR_output_keys.
    intros.
    eapply filterMap_In; eauto. auto.
  Qed.

  Lemma get_IR_input_keys_complete :
    forall xs k,
      In (IRI k) xs ->
      In k (get_IR_input_keys xs).
  Proof.
    unfold get_IR_input_keys.
    intros.
    eapply filterMap_In; eauto. auto.
  Qed.

  Lemma op_equivalent_all_Is_O_middle :
    forall xs ys k,
      (forall k', In (I k') xs -> k <> k') ->
      op_equivalent (xs ++ O k :: ys) (O k :: xs ++ ys).
  Proof.
    intros.
    rewrite app_comm_cons.
    replace (xs ++ O k :: ys) with ((xs ++ [O k]) ++ ys) by now rewrite app_ass.
    auto using op_equiv_app_tail, op_equivalent_all_Is_O.
  Qed.

  Lemma NoDup_get_op_output_keys_In_O :
    forall xs ys k,
      NoDup (get_op_output_keys (xs ++ O k :: ys)) ->
      In (O k) (xs ++ ys) ->
      False.
  Proof.
    intros.
    rewrite get_op_output_keys_app in *.
    rewrite get_op_output_keys_defn in *.
    do_in_app.
    intuition; eapply NoDup_remove_2; eauto using get_op_output_keys_complete, in_or_app.
  Qed.

  Lemma NoDup_get_op_output_keys_In_2_3 :
    forall xs ys zs k,
      NoDup (get_op_output_keys (xs ++ I k :: ys ++ O k :: zs)) ->
      In (O k) (xs ++ ys ++ zs) ->
      False.
  Proof.
    intros.
    rewrite get_op_output_keys_app in *.
    rewrite get_op_output_keys_defn in *.
    rewrite get_op_output_keys_app in *.
    rewrite get_op_output_keys_defn in *.
    repeat
      (do_in_app; intuition
                    eauto using NoDup_app3_not_in_1, NoDup_app3_not_in_2,
                  NoDup_app3_not_in_3, get_op_output_keys_complete).
  Qed.

  Lemma NoDup_get_op_input_keys_In_2_3 :
    forall xs ys zs k,
      NoDup (get_op_input_keys (xs ++ I k :: ys ++ O k :: zs)) ->
      In (I k) (xs ++ ys ++ zs) ->
      False.
  Proof.
    intros.
    rewrite get_op_input_keys_app in *.
    rewrite get_op_input_keys_defn in *.
    rewrite get_op_input_keys_app in *.
    rewrite get_op_input_keys_defn in *.
    match goal with
      | [ H : NoDup _ |- _ ] =>
        apply NoDup_remove_2 in H
    end.
    repeat (do_in_app; intuition); eauto 10 using get_op_input_keys_complete with *.
  Qed.

  Lemma O_IRO_preserved_IU :
    forall xs ys k' ir,

      (forall k, In (O k) (xs ++ I k' :: ys) ->
                 In (IRO k) (IRI k' :: IRU k' :: ir)) ->
      forall k, In (O k) (xs ++ ys) ->
                In (IRO k) ir.
  Proof.
    intros.
    eapply In_cons_neq.
    - eapply In_cons_neq.
      + eauto.
      + discriminate.
    - discriminate.
  Qed.

  Lemma O_IRO_preserved :
    forall xs ys zs k' ir,
      NoDup (get_op_output_keys (xs ++ I k' :: ys ++ O k' :: zs)) ->
      (forall k, In (O k) (xs ++ I k' :: ys ++ O k' :: zs) ->
                 In (IRO k) (IRI k' :: IRO k' :: ir)) ->
      forall k, In (O k) (xs ++ ys ++ zs) ->
                In (IRO k) ir.
  Proof.
    intros.
    eapply In_cons_neq.
    - eapply In_cons_neq.
      + eauto using In_cons_2_3.
      + discriminate.
    - intro. find_inversion. eauto using NoDup_get_op_output_keys_In_2_3.
  Qed.

  Lemma no_Ik_in_first2 :
    forall xs ys zs k,
      NoDup (get_op_input_keys (xs ++ I k :: ys ++ O k :: zs)) ->
      forall k',
        In (I k') (xs ++ ys) -> k <> k'.
  Proof.
    intros.
    rewrite get_op_input_keys_app in *. rewrite get_op_input_keys_defn in *.
    match goal with
      | [ H : NoDup (_ ++ _ :: _) |- _ ] =>
        apply NoDup_remove_2 in H
    end.
    rewrite get_op_input_keys_app in *.
    intro. subst.

    repeat do_in_app; intuition auto 10 using get_op_input_keys_complete, in_or_app.
  Qed.

  Lemma IRO_O_preserved_IU :
    forall xs ys k' ir,
      (forall k, In (IRO k) (IRI k' :: IRU k' :: ir) ->
                 In (O k) (xs ++ I k' :: ys)) ->
      forall k, In (IRO k) ir ->
                In (O k) (xs ++ ys).
  Proof.
    intros.
    apply in_middle_reduce with (y := I k'); intuition (auto with *; congruence).
  Qed.

  Lemma IRO_O_preserved :
    forall xs ys zs k' ir,
      (~ In k' (get_IR_output_keys ir)) ->
      (forall k, In (IRO k) (IRI k' :: IRO k' :: ir) ->
                 In (O k) (xs ++ I k' :: ys ++ O k' :: zs)) ->
      forall k, In (IRO k) ir ->
                In (O k) (xs ++ ys ++ zs).
  Proof.
    intros.

    eapply In_cons_2_3_neq; eauto using in_cons; try congruence.
    intro. find_inversion. eauto using get_IR_output_keys_complete_O.
  Qed.

  Lemma IRU_I_preserved_IU :
    forall xs ys k' ir,
      (~ In k' (get_IR_output_keys ir)) ->
      (forall k, In (IRU k) (IRI k' :: IRU k' :: ir) ->
                 In (I k) (xs ++ I k' :: ys)) ->
      forall k, In (IRU k) ir ->
                In (I k) (xs ++ ys).
  Proof.
    intros.
    apply in_middle_reduce with (y := I k'); intuition.
    find_inversion.
    auto using get_IR_output_keys_complete_U.
  Qed.

  Lemma IRU_I_preserved :
    forall xs ys zs k' ir,
      (~ In k' (get_IR_output_keys ir)) ->
      (forall k, In (IRU k) (IRI k' :: IRO k' :: ir) ->
                 In (I k) (xs ++ I k' :: ys ++ O k' :: zs)) ->
      forall k, In (IRU k) ir ->
                In (I k) (xs ++ ys ++ zs).
  Proof.
    intros.
    eapply In_cons_2_3_neq; eauto using in_cons; try congruence.
    intro. find_inversion. eauto using get_IR_output_keys_complete_U.
  Qed.

  Lemma NoDup_get_op_input_keys_In_I :
    forall xs ys k,
      NoDup (get_op_input_keys (xs ++ I k :: ys)) ->
      In (I k) (xs ++ ys) -> False.
  Proof.
    intros.
    rewrite get_op_input_keys_app in *.
    rewrite get_op_input_keys_defn in *.
    do_in_app.
    intuition; eapply NoDup_remove_2; eauto using get_op_input_keys_complete, in_or_app.
  Qed.

  Lemma in_before_before_preserved_IU :
    forall xs ys k ir,
      NoDup (get_op_input_keys (xs ++ I k :: ys)) ->
      (forall k1 k2,
         In (I k2) (xs ++ I k :: ys) ->
         before (O k1) (I k2) (xs ++ I k :: ys) ->
         before (IRO k1) (IRI k2) (IRI k :: IRU k :: ir)) ->
      forall k1 k2,
        In (I k2) (xs ++ ys) ->
        before (O k1) (I k2) (xs ++ ys) ->
        before (IRO k1) (IRI k2) ir.
  Proof.
    intros.
    simpl in *.
    find_eapply_lem_hyp before_middle_insert.
    - find_eapply_lem_hyp in_middle_insert.
      eapply_prop_hyp In (O k1); eauto.
      intuition; try congruence.
    - intro. find_inversion. eauto using NoDup_get_op_input_keys_In_I.
  Qed.

  Lemma in_before_before_preserved :
    forall xs ys zs k ir,
      NoDup (get_op_input_keys (xs ++ I k :: ys ++ O k :: zs)) ->
      NoDup (get_op_output_keys (xs ++ I k :: ys ++ O k :: zs)) ->
      (forall k1 k2,
         In (I k2) (xs ++ I k :: ys ++ O k :: zs) ->
         before (O k1) (I k2) (xs ++ I k :: ys ++ O k :: zs) ->
         before (IRO k1) (IRI k2) (IRI k :: IRO k :: ir)) ->
      forall k1 k2,
        In (I k2) (xs ++ ys ++ zs) ->
        before (O k1) (I k2) (xs ++ ys ++ zs) ->
        before (IRO k1) (IRI k2) ir.
  Proof.
    intros.
    simpl in *.
    find_copy_eapply_lem_hyp before_2_3_insert.
    - find_eapply_lem_hyp In_cons_2_3.
      eapply_prop_hyp In (O k1); eauto.
      intuition; try congruence.
      find_inversion.
      find_copy_eapply_lem_hyp before_In.
      exfalso.
      eauto using NoDup_get_op_output_keys_In_2_3.
    - intro. find_inversion. eauto using NoDup_get_op_input_keys_In_2_3.
    - discriminate.
  Qed.

  Lemma in_before_preserved_IU :
    forall xs ys k',
      ~ acknowledged_op k' (xs ++ ys) ->
      (forall k, In (O k) (xs ++ I k' :: ys) ->
                 before (I k) (O k) (xs ++ I k' :: ys)) ->
      forall k, In (O k) (xs ++ ys) ->
                before (I k) (O k) (xs ++ ys).
  Proof.
    intros.
    eapply before_middle_reduce.
    - eauto using in_middle_insert.
    - intro. find_inversion. intuition eauto using acknowledged_op_defn.
  Qed.

  Lemma in_before_preserved :
    forall xs ys zs k',
      NoDup (get_op_output_keys (xs ++ I k' :: ys ++ O k' :: zs)) ->
      (forall k, In (O k) (xs ++ I k' :: ys ++ O k' :: zs) ->
                 before (I k) (O k) (xs ++ I k' :: ys ++ O k' :: zs)) ->
      forall k, In (O k) (xs ++ ys ++ zs) ->
                before (I k) (O k) (xs ++ ys ++ zs).
  Proof.
    intros.
    eapply before_2_3_reduce.
    - eauto using In_cons_2_3.
    - intro. find_inversion. eauto using NoDup_get_op_output_keys_In_2_3.
    - discriminate.
  Qed.

  Lemma IRI_I_preserved_IU :
    forall xs ys k' ir,
      (~ In k' (get_IR_input_keys ir)) ->
      (forall k, In (IRI k) (IRI k' :: IRU k' :: ir) -> In (I k) (xs ++ I k' :: ys)) ->
      forall k, In (IRI k) ir -> In (I k) (xs ++ ys).
  Proof.
    intros.
    eapply in_middle_reduce.
    - auto with *.
    - intro. find_inversion.  eauto using get_IR_input_keys_complete.
  Qed.

  Lemma IRI_I_preserved :
    forall xs ys zs k' ir,
      (~ In k' (get_IR_input_keys ir)) ->
      (forall k, In (IRI k) (IRI k' :: IRO k' :: ir) -> In (I k) (xs ++ I k' :: ys ++ O k' :: zs)) ->
      forall k, In (IRI k) ir -> In (I k) (xs ++ ys ++ zs).
  Proof.
    intros.
    eapply In_cons_2_3_neq.
    - auto with *.
    - intro. find_inversion. eauto using get_IR_input_keys_complete.
    - discriminate.
  Qed.

  Lemma subseq_get_op_input_keys :
    forall xs ys,
      subseq xs ys ->
      subseq (get_op_input_keys xs) (get_op_input_keys ys).
  Proof.
    eauto using subseq_filterMap.
  Qed.

  Lemma subseq_get_op_output_keys :
    forall xs ys,
      subseq xs ys ->
      subseq (get_op_output_keys xs) (get_op_output_keys ys).
  Proof.
    eauto using subseq_filterMap.
  Qed.

  Ltac start :=
    match goal with
      | [ H : good_trace (_ :: _) |- _ ] => simpl in H
    end;
    break_and; subst;
    match goal with
      | [ H : context [In (?c _) (_ :: ?c ?k' :: _) -> In _ ?l] |- _ ] =>
        assert (In (O k') l) by firstorder;
          assert (before (I k') (O k') l) by auto;
          repeat rewrite get_IR_input_keys_defn in *;
          repeat rewrite get_IR_output_keys_defn in *;
          repeat match goal with
                   | [ H : NoDup (_ :: _) |- _ ] => invc H
                 end;
          assert (In (I k') l) by eauto using before_In;
          assert (forall x, before x (I k') l -> exists k, x = I k) by eauto using before_head_op;
          find_copy_apply_lem_hyp before_split; auto; try congruence; break_exists; subst
    end;
    repeat match goal with
             | [ H : In ?x (_ ++ ?x :: _) |- _ ] => clear H
             | [ H : In ?x (_ ++ _ :: _ ++ ?x :: _) |- _ ] => clear H
           end.

  Lemma acknowledge_all_ops_func_target_ext_strong :
    forall (l : list op) (t t' : list IR),
      (forall k : K, In (I k) l -> In (IRU k) t -> In (IRU k) t') ->
      (forall k : K, In (I k) l -> In (IRU k) t' -> In (IRU k) t) ->
      acknowledge_all_ops_func l t = acknowledge_all_ops_func l t'.
  Proof.
    induction l; intros.
    - auto.
    - simpl. repeat break_match; subst; simpl in *; intuition auto 10 using f_equal with *.
      + exfalso. eauto.
      + exfalso. eauto.
  Qed.

  Lemma IRU_not_O_preserved_IU :
    forall xs ys k' ir,
      (forall k,
         In (IRU k) (IRI k' :: IRU k' :: ir) ->
         ~ In (O k) (xs ++ I k' :: ys)) ->
      forall k,
        In (IRU k) (ir) ->
        ~ In (O k) (xs ++ ys).
  Proof.
    intuition.
    eapply H.
    - apply in_cons. apply in_cons. eauto.
    - auto using in_middle_insert.
  Qed.

  Lemma IRU_not_O_preserved :
    forall xs ys zs k' ir,
      (forall k,
         In (IRU k) (IRI k' :: IRO k' :: ir) ->
         ~ In (O k) (xs ++ I k' :: ys ++ O k' :: zs)) ->
      forall k,
        In (IRU k) (ir) ->
        ~ In (O k) (xs ++ ys ++ zs).
  Proof.
    intuition.
    eapply H.
    - eauto with *.
    - auto using In_cons_2_3.
  Qed.


  Lemma IR_equivalent_acknowledge_all_ops_func :
    forall ir,
      good_trace ir ->
      forall l,
        (forall k, In (O k) l -> In (IRO k) ir) ->
        (forall k, In (IRO k) ir -> In (O k) l) ->
        (forall k, In (IRU k) ir -> In (I k) l) ->
        (forall k, In (IRU k) ir -> ~ In (O k) l) ->
        (forall k k', In (I k') l ->
                      before (O k) (I k') l ->
                      before (IRO k) (IRI k') ir) ->
        (forall k, In (O k) l -> before (I k) (O k) l) ->
        (forall k, In (IRI k) ir -> In (I k) l) ->
        NoDup (get_op_input_keys l) ->
        NoDup (get_IR_input_keys ir) ->
        NoDup (get_op_output_keys l) ->
        NoDup (get_IR_output_keys ir) ->
        IR_equivalent (acknowledge_all_ops_func l ir) ir.
  Proof.
    intros ir.
    induction ir, good_trace using good_trace_ind; intros; try solve [simpl in *; intuition].
    - rewrite acknowledge_all_ops_func_target_nil; auto.
    - start.
      eapply IR_equiv_trans.
      + apply op_equiv_AAOF_IR_equiv.
        apply op_equivalent_all_Is_I_middle.
        intros.
        match goal with
          | [ H : context [before] |- _ ] => apply H
        end.
        apply In_app_before; auto using op_eq_dec.
        find_rewrite_lem get_op_input_keys_app. rewrite get_op_input_keys_defn in *.
        intro. eapply NoDup_remove_2; eauto using in_or_app, get_op_input_keys_complete.
      + repeat rewrite app_ass.
        rewrite acknowledge_all_ops_func_defn.
        break_if.
        * constructor.
          { eapply IR_equiv_trans.
            - apply op_equiv_AAOF_IR_equiv.
              rewrite <- app_ass.
              eauto using op_equivalent_all_Is_O_middle, no_Ik_in_first2.
            - simpl. constructor.
              rewrite acknowledge_all_ops_func_target_ext with (t' := ir).
              + rewrite app_ass.
                apply IHP; auto.
                * eauto using O_IRO_preserved.
                * eauto using IRO_O_preserved.
                * eauto using IRU_I_preserved.
                * eauto using IRU_not_O_preserved.
                * eauto using in_before_before_preserved.
                * eauto using in_before_preserved.
                * eauto using IRI_I_preserved.
                * eauto using subseq_NoDup, subseq_get_op_input_keys, subseq_2_3.
                * eauto using subseq_NoDup, subseq_get_op_output_keys, subseq_2_3.
              + simpl. intuition congruence.
              + intuition.
          }
        * { break_if.
            - simpl in *. intuition (try congruence).
              exfalso. eauto using get_IR_output_keys_complete_U.
            - exfalso. apply n. red. intuition.
          }
    - (* IRU case. *)
      match goal with
        | [ H : good_trace (_ :: _) |- _ ] => simpl in H
      end.
      break_and; subst.
      match goal with
        | [ H : context [In (?c _) (_ :: ?c ?k' :: _) -> In _ ?l] |- _ ] =>
          assert (In (I k') l) by firstorder;
            assert (forall x, before x (I k') l -> exists k, x = I k) by eauto using before_head_op
      end;
        repeat rewrite get_IR_input_keys_defn in *;
        repeat rewrite get_IR_output_keys_defn in *;
        repeat match goal with
                 | [ H : NoDup (_ :: _) |- _ ] => invc H
               end.
      find_copy_apply_lem_hyp in_split.
      break_exists. subst.
      eapply IR_equiv_trans.
      + apply op_equiv_AAOF_IR_equiv.
        apply op_equivalent_all_Is_I_middle.
        intros.
        match goal with
          | [ H : context [before] |- _ ] => apply H
        end.
        apply In_app_before; auto using op_eq_dec.
        find_rewrite_lem get_op_input_keys_app. rewrite get_op_input_keys_defn in *.
        intro. eapply NoDup_remove_2; eauto using in_or_app, get_op_input_keys_complete.
      + rewrite acknowledge_all_ops_func_defn.
        break_if.
        * exfalso.
          intuition eauto using in_middle_insert, in_cons, in_eq, acknowledged_op_defn.
        * rewrite if_decider_true by intuition.
          { constructor. constructor.
            rewrite acknowledge_all_ops_func_target_ext_strong with (t' := ir).
            - apply IHP; auto.
              + eauto using O_IRO_preserved_IU.
              + eauto using IRO_O_preserved_IU.
              + eauto using IRU_I_preserved_IU.
              + eauto using IRU_not_O_preserved_IU.
              + eauto using in_before_before_preserved_IU.
              + eauto using in_before_preserved_IU.
              + eauto using IRI_I_preserved_IU.
              + eauto using subseq_NoDup, subseq_get_op_input_keys, subseq_middle.
              + eauto using subseq_NoDup, subseq_get_op_output_keys, subseq_middle.
            - simpl. intuition (try congruence ). find_inversion.
              rewrite get_op_input_keys_app in *. rewrite get_op_input_keys_defn in *.
              exfalso.
              repeat match goal with
                       | [ H : In ?x (_ ++ ?x :: _) |- _ ] => clear H
                       | [ H : In ?x (_ ++ _ :: _ ++ ?x :: _) |- _ ] => clear H
                     end.
              do_in_app.
              eapply NoDup_remove_2; intuition eauto using in_or_app, get_op_input_keys_complete.
            - intros. simpl. intuition.
          }
  Qed.

  Theorem equivalent_intro :
    forall l ir,
      good_trace ir ->
      (forall k, In (O k) l -> In (IRO k) ir) ->
      (forall k, In (IRO k) ir -> In (O k) l) ->
      (forall k, In (IRU k) ir -> In (I k) l) ->
      (forall k k', In (I k') l ->
                    before (O k) (I k') l ->
                    before (IRO k) (IRI k') ir) ->
      (forall k, In (O k) l -> before (I k) (O k) l) ->
      (forall k, In (IRU k) ir -> ~ In (O k) l) ->
      NoDup (get_op_input_keys l) ->
      NoDup (get_IR_input_keys ir) ->
      NoDup (get_op_output_keys l) ->
      NoDup (get_IR_output_keys ir) ->
      equivalent l ir.
  Proof.
    intros.
    red.
    intuition.
    exists (acknowledge_all_ops_func l ir).
    intuition.
    - apply acknowledge_all_ops_func_correct.
    - apply IR_equivalent_acknowledge_all_ops_func; auto.
      intros.
      find_apply_lem_hyp good_trace_IRI_in; auto.
      intuition eauto using before_In.
  Qed.

End Linearizability.
Arguments I {_} _.
Arguments O {_} _.

Arguments IRI {_} _.
Arguments IRO {_} _.
Arguments IRU {_} _.
