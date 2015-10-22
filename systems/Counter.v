Require Import List.
Import ListNotations.

Require Import Arith.
Require Import Omega.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Set Implicit Arguments.

Section Counter.
  Inductive Name := primary | backup.
  Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Inductive Msg := inc | ack.
  Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Inductive Input := request_inc.
  Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
    destruct x,y. auto.
  Defined.

  Inductive Output := inc_executed.
  Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
    destruct x,y. auto.
  Defined.

  Definition Data := nat.

  Definition init_Data := 0.

  Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

  Definition PrimaryNetHandler (m : Msg) : Handler Data :=
    match m with
    | ack => write_output inc_executed
    | _ => nop
    end.

  Definition PrimaryInputHandler (i : Input) : Handler Data :=
    match i with
    | request_inc => modify S ;; send (backup, inc)
    end.

  Definition BackupNetHandler (m : Msg) : Handler Data :=
    match m with
    | inc => modify S ;; send (primary, ack)
    | _ => nop
    end.

  Definition BackupInputHandler (i : Input) : Handler Data := nop.

  Definition NetHandler (me : Name) (m : Msg) : Handler Data :=
    match me with
    | primary => PrimaryNetHandler m
    | backup => BackupNetHandler m
    end.

  Definition InputHandler (me : Name) (i : Input) : Handler Data :=
    match me with
    | primary => PrimaryInputHandler i
    | backup => BackupInputHandler i
    end.

  Instance Counter_BaseParams : BaseParams :=
    {
      data := Data;
      input := Input;
      output := Output
    }.

  Definition Nodes : list Name := [primary; backup].

  Lemma all_Names_Nodes : forall n, In n Nodes.
  Proof.
    destruct n; simpl; auto.
  Qed.

  Lemma NoDup_Nodes : NoDup Nodes.
  Proof.
    repeat constructor; simpl; intuition discriminate.
  Qed.

  Instance Counter_MultiParams : MultiParams Counter_BaseParams :=
    {
      name := Name;
      name_eq_dec := Name_eq_dec;
      msg := Msg;
      msg_eq_dec := Msg_eq_dec;
      nodes := Nodes;
      all_names_nodes := all_Names_Nodes;
      no_dup_nodes := NoDup_Nodes;
      init_handlers := fun _ => init_Data;
      net_handlers := fun dst src msg s =>
                        runGenHandler_ignore s (NetHandler dst msg);
      input_handlers := fun nm i s =>
                        runGenHandler_ignore s (InputHandler nm i)
    }.


  Lemma net_handlers_NetHandler :
    forall h src m d os d' ms,
      net_handlers h src m d = (os, d', ms) ->
      NetHandler h m d = (tt, os, d', ms).
  Proof.
    intros.
    simpl in *.
    monad_unfold.
    repeat break_let.
    find_inversion.
    destruct u. auto.
  Qed.

  Lemma input_handlers_InputHandlers :
    forall h i d os d' ms,
      input_handlers h i d = (os, d', ms) ->
      InputHandler h i d = (tt, os, d', ms).
  Proof.
    intros.
    simpl in *.
    monad_unfold.
    repeat break_let.
    find_inversion.
    destruct u. auto.
  Qed.

  Lemma PrimaryNetHandler_no_msgs :
    forall m d ms d' o u,
      PrimaryNetHandler m d = (u, o, d', ms) ->
      ms = [].
  Proof.
    unfold PrimaryNetHandler.
    intros. monad_unfold.
    break_match; find_inversion; auto.
  Qed.

  Definition in_flight (l : list packet) : nat :=
    length (filterMap
              (fun p => if msg_eq_dec (pBody p) inc
                     then if name_eq_dec (pDst p) backup
                          then Some tt else None
                     else None)
              l).

  Lemma in_flight_app :
    forall xs ys,
      in_flight (xs ++ ys) = in_flight xs + in_flight ys.
  Proof.
    intros.
    unfold in_flight.
    rewrite filterMap_app.
    rewrite app_length.
    auto.
  Qed.

  Lemma in_flight_cons_primary_dst :
    forall p,
      pDst p = primary ->
      in_flight [p] = 0.
  Proof.
    intros.
    unfold in_flight.
    simpl.
    repeat break_match; try congruence; auto.
  Qed.

  Lemma in_flight_nil :
    in_flight [] = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma InputHandler_in_flight_preserved :
    forall h i d u o d' l,
      InputHandler h i d = (u, o, d', l) ->
      d' = d + in_flight (send_packets h l).
  Proof.
    unfold InputHandler, PrimaryInputHandler, BackupInputHandler.
    simpl.
    intros.
    monad_unfold.
    repeat break_match; find_inversion; compute; auto.
    rewrite plus_comm. auto.
  Qed.

  Lemma NetHandler_in_flight_preserved :
    forall p d u o d' l,
      NetHandler (pDst p) (pBody p) d = (u, o, d', l) ->
      d' + in_flight (send_packets (pDst p) l) = d + in_flight [p].
  Proof.
    unfold NetHandler, PrimaryNetHandler, BackupNetHandler.
    intros.
    monad_unfold.
    destruct p. simpl in *.
    repeat break_match; find_inversion; simpl; try rewrite in_flight_nil;
    unfold Data in *; compute;
    auto with *.
  Qed.

  Lemma InputHandler_backup_no_msgs :
    forall i d u o d' l,
      InputHandler backup i d = (u, o, d', l) ->
      l = [].
  Proof.
    simpl. unfold BackupInputHandler.
    intros.
    monad_unfold.
    find_inversion.
    auto.
  Qed.

  Lemma cons_is_app :
    forall A (x : A) xs,
      x :: xs = [x] ++ xs.
  Proof.
    auto.
  Qed.

  Lemma backup_plus_network_eq_primary :
    forall net tr,
      step_m_star (params := Counter_MultiParams) step_m_init net tr ->
      nwState net backup + in_flight (nwPackets net) = nwState net primary.
  Proof.
    intros.
    remember step_m_init as y in *.
    revert Heqy.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - reflexivity.
    - concludes.
      match goal with
      | [ H : step_m _ _ _ |- _ ] => invc H
      end; simpl.
      + find_apply_lem_hyp net_handlers_NetHandler.
        find_copy_apply_lem_hyp NetHandler_in_flight_preserved.
        repeat find_rewrite.
        rewrite cons_is_app in IHrefl_trans_1n_trace1.
        repeat rewrite in_flight_app in *.
        destruct (pDst p) eqn:?;
                 try rewrite update_same;
          try rewrite update_diff by congruence;
          unfold send_packets in *; simpl in *.
        * erewrite PrimaryNetHandler_no_msgs with (ms := l) in * by eauto.
          rewrite in_flight_cons_primary_dst in * by auto.
          simpl in *. rewrite in_flight_nil in *. auto with *.
        * omega.
      + find_apply_lem_hyp input_handlers_InputHandlers.
        find_copy_apply_lem_hyp InputHandler_in_flight_preserved.
        unfold send_packets in *. simpl in *.
        rewrite in_flight_app. subst.
        destruct h eqn:?;
                 try rewrite update_same;
          try rewrite update_diff by congruence.
        * omega.
        * erewrite InputHandler_backup_no_msgs with (l := l) by eauto.
          simpl. rewrite in_flight_nil. omega.
  Qed.

  Theorem primary_ge_backup :
    forall net tr,
      step_m_star (params := Counter_MultiParams) step_m_init net tr ->
      nwState net backup <= nwState net primary.
  Proof.
    intros.
    apply backup_plus_network_eq_primary in H.
    auto with *.
  Qed.
End Counter.