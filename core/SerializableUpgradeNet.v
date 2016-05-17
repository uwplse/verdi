Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Cheerios.ComplexSerializers.
Require Import Cheerios.Combinators.
Require Import Cheerios.Types.
Require String.
Notation string := String.string.

Definition bytes := list bool.
Definition empty : bytes := [].

Notation input := bytes (only parsing).
Notation msg := bytes (only parsing).
Notation output := bytes (only parsing).
Notation state := bytes (only parsing).

Local Arguments serialize : simpl never.
Local Arguments deserialize : simpl never.

Set Implicit Arguments.

Record version (name : Type) : Type :=
  Version {
    handleInput : name -> input -> state -> state * list (name * msg) * list output;
    handleMsg : name -> msg -> state -> state * list (name * msg) * list output;
  }.

Class Eq (A : Type) :=
  {
    eq_dec : forall x y : A, {x = y} + {x <> y}
  }.

Definition update {A} {eqA : Eq A} {B} (f : A -> B) (a : A) (b : B) : A -> B :=
  fun a' => if eq_dec a a' then b else f a'.

Lemma update_same : forall {A} {eqA : Eq A} {B} (f : A -> B) (a : A) (b : B),
    update(eqA := eqA) f a b a = b.
Proof.
  unfold update.
  intros. break_if; congruence.
Qed.

Lemma update_neq : forall {A} {eqA : Eq A} {B} (f : A -> B) (a1 a2 : A) (b : B),
    a1 <> a2 ->
    update(eqA := eqA) f a1 b a2 = f a2.
Proof.
  unfold update.
  intros.
  break_if; congruence.
Qed.

Section upgrade.
  Variable name : Type.
  Context {Ename : Eq name}.
  Variable versions : list ((state -> option state) * version name).

  Record world :=
    World {
      localState : name -> state;
      nextVersion : name -> nat;
      packets : list (name * msg);
      trace : list (name * (input + output))
    }.

  Definition initial_world : world :=
    World (fun _ => empty) (fun _ => 0) [] [].

  Inductive step : world -> world -> Prop :=
  | Upgrade : forall w w' h u v st',
      nth_error versions (nextVersion w h) = Some (u,v) ->
      u (localState w h) = Some st' ->
      w' = World (update (localState w) h st')
                 (update (nextVersion w) h (S (nextVersion w h)))
                 (packets w)
                 (trace w) ->
      step w w'
  | Deliver : forall w w' h m xs ys n u v st' ms os,
      packets w = xs ++ (h,m) :: ys ->
      nextVersion w h = S n ->
      nth_error versions n = Some (u, v) ->
      handleMsg v h m (localState w h) = (st', ms, os) ->
      w' = World (update (localState w) h st')
                 (nextVersion w)
                 (ms ++ xs ++ ys)
                 (trace w ++ map (fun o => (h, inr o)) os) ->
      step w w'
  | Input : forall w w' h i n u v st' ms os,
      nextVersion w h = S n ->
      nth_error versions n = Some (u, v) ->
      handleInput v h i (localState w h) = (st', ms, os) ->
      w' = World (update (localState w) h st')
                 (nextVersion w)
                 (ms ++ packets w)
                 (trace w ++ [(h, inl i)] ++ map (fun o => (h, inr o)) os) ->
      step w w'
  .

  Definition wpred := world -> Prop.
  Definition wlift (P : Prop) : wpred := fun _ => P.
  Definition wand (P Q : wpred) : wpred := fun w => P w /\ Q w.
  Definition wor (P Q : wpred) : wpred := fun w => P w \/ Q w.
  Definition wimp (P Q : wpred) : wpred := fun w => P w -> Q w.

  Inductive reachable : wpred :=
  | reachInit : reachable initial_world
  | reachStep : forall w w',
      reachable w ->
      step w w' ->
      reachable w'.

  Definition invariant (P : wpred) :=
    forall w,
      reachable w ->
      P w.

  Definition hoare (P Q : wpred) :=
    forall w w',
      P w ->
      step w w' ->
      Q w'.

  Definition inductive (P : wpred) :=
    P initial_world /\
    hoare P P.

  Lemma inductive_invariant :
    forall P,
      inductive P ->
      invariant P.
  Proof.
    intros. unfold inductive, invariant, hoare in *.
    intros.
    match goal with
    | H : context [reachable] |- _ =>
      induction H
    end; firstorder.
  Qed.

  Lemma invariant_and :
    forall P Q,
      invariant P ->
      invariant Q ->
      invariant (wand P Q).
  Proof.
    intros. 
    firstorder.
  Qed.

  Definition step_star := Relation_Operators.clos_refl_trans_n1 _ step.

  Definition step_reachable w := step_star initial_world w.

  Lemma step_reachable_ind :
    forall (P : world -> Prop),
      P initial_world ->
      (forall w1 w2,
          step_reachable w1 ->
          step w1 w2 ->
          P w1 ->
          P w2) ->
      forall w, step_reachable w -> P w.
  Proof.
    intros.
    induction H1; eauto.
  Qed.
End upgrade.


Module PBKV.
  Inductive name := Primary | Backup.
  Instance Eq_name : Eq name.
  Proof.
    constructor.
    decide equality.
  Defined.

  Module VersionOne.
    Inductive input := Put (k v : string) | Get (k : string).
    Definition input_serialize (i : input) : bytes :=
      serialize 0 ++
      match i with
      | Put k v => serialize true ++ serialize k ++ serialize v
      | Get k => serialize false ++ serialize k
      end.
    Definition input_deserialize (bs : bytes) : option (input * bytes) :=
      match deserialize bs with None => None
      | Some (ver, rest) =>
        if Nat.eq_dec ver 0
        then
          match deserialize rest with None => None
          | Some (b, rest) =>
          match deserialize rest with None => None
          | Some (k, rest) =>
              if b:bool then
                match deserialize rest with None => None
                | Some (v, rest) => Some (Put k v, rest)
                end
              else
                Some (Get k, rest)
          end
          end
        else None
      end.
    Instance input_Serializer : Serializer input :=
      {| serialize := input_serialize;
         deserialize := input_deserialize
      |}.
    unfold input_serialize, input_deserialize.
    intros.
    destruct x;
       rewrite !app_assoc_reverse;
       now rewrite !Serialize_reversible.
    Defined.

    Inductive msg := Cmd (i : input) | Ack.
    Definition msg_serialize (m : msg) : bytes :=
      serialize 0 ++
      match m with
      | Cmd i => serialize true ++ serialize i
      | Ack => serialize false
      end.
    Definition msg_deserialize (bs : bytes) : option (msg * bytes) :=
        match deserialize bs with None => None
        | Some (ver, rest)  =>
        match deserialize rest with None => None
        | Some (b, rest) =>
          if Nat.eq_dec ver 0
          then if b:bool
               then match deserialize rest with None => None
                                           | Some (i, rest) => Some (Cmd i, rest)
                    end
               else Some (Ack, rest)
          else None
        end
        end.
    Instance msg_Serializer : Serializer msg :=
      {| serialize := msg_serialize;
         deserialize := msg_deserialize
      |}.
    unfold msg_serialize, msg_deserialize.
    intros.
    destruct x;
      rewrite !app_assoc_reverse;
      now rewrite !Serialize_reversible.
    Defined.

    Inductive output := ResGet (k v : string) | ResPut (k old_v v : string).
    Definition output_serialize (o : output) : bytes :=
      serialize 0 ++
      match o with
      | ResGet k v => serialize true ++ serialize k ++ serialize v
      | ResPut k old_v v => serialize false ++ serialize k ++ serialize old_v ++ serialize v
      end.
    Definition output_deserialize (bs : bytes) : option (output * bytes) :=
      match deserialize bs with None => None
      | Some (ver, rest) =>
        if Nat.eq_dec ver 0
        then
          match deserialize rest with None => None
          | Some (b, rest) =>
            if b:bool
            then
              match deserialize rest with None => None
              | Some (k, rest) =>
              match deserialize rest with None => None
              | Some (v, rest) => Some (ResGet k v, rest)
              end
              end
            else
              match deserialize rest with None => None
              | Some (k, rest) =>
              match deserialize rest with None => None
              | Some (old_v, rest) =>
              match deserialize rest with None => None
              | Some (v, rest) => Some (ResPut k old_v v, rest)
              end
              end
              end
          end
        else None
      end.
    Instance output_Serializer : Serializer output :=
      {| serialize := output_serialize;
         deserialize := output_deserialize
      |}.
    unfold output_serialize, output_deserialize.
    intros.
    destruct x;
      rewrite !app_assoc_reverse;
      now rewrite !Serialize_reversible.
    Defined.

    Record data := Data { db : list (string * string);
                          log : list input;
                          nextIndex : nat
                        }.
    Definition data_serialize (d : data) : bytes :=
      serialize (db d) ++ serialize (log d) ++ serialize (nextIndex d).
    Definition data_deserialize (bs : bytes) : option (data * bytes) :=
      match deserialize bs with None => None
      | Some (db, rest) =>
      match deserialize rest with None => None
      | Some (log, rest) =>
      match deserialize rest with None => None
      | Some (ni, rest) => Some (Data db log ni, rest)
      end
      end
      end.
    Instance data_Serializer : Serializer data :=
      {| serialize := data_serialize;
         deserialize := data_deserialize
      |}.
    unfold data_serialize, data_deserialize.
    intros.
    destruct x.
    rewrite !app_assoc_reverse.
    now rewrite !Serialize_reversible.
    Defined.

    Definition nop (s : bytes) : bytes * list (name * bytes) * list bytes := (s, [], []).

    Definition handleInput (n : name) (i : bytes) (s : bytes) :
        bytes * list (name * bytes) * list bytes :=
      match deserialize s with None => nop s
      | Some (s, _) =>
      match deserialize i with None => nop (serialize s)
      | Some (i, _) =>
      match n with
      | Primary =>
        let log' := log s ++ [i] in
        let ms := if Nat.eq_dec (length (log s)) (nextIndex s)
                  then [(Backup, serialize (Cmd i))]
                  else [] in
        (serialize (Data (db s) log' (nextIndex s)), ms, [])
      | Backup => nop (serialize s)
      end
      end
      end.

    Definition execute (i : input) (db : list (string * string))
        : output * list (string * string) :=
      match i with
      | Put k v => let old_v := assoc_default String.string_dec db String.EmptyString k in
                  let db' := assoc_set String.string_dec db k v in
                  (ResPut k old_v v, db')
      | Get k => let v := assoc_default String.string_dec db String.EmptyString k in
                (ResGet k v, db)
      end.

    Definition handleMsg (n : name) (m : bytes) (s : bytes) :
        bytes * list (name * bytes) * list bytes :=
      match deserialize s with None => nop s
      | Some (s, _) =>
      match deserialize m with None => nop (serialize s)
      | Some (m, _) =>
      match n, m with
      | Primary, Ack =>
        match nth_error (log s) (nextIndex s) with None => nop (serialize s)
        | Some i => let (o, db') := execute i (db s) in
                   let ni' := S (nextIndex s) in
                   let ms := match nth_error (log s) ni' with
                             | None => []
                             | Some i' => [(Backup, serialize (Cmd i'))]
                             end
                   in (serialize (Data db' (log s) ni'), ms, [serialize o])
        end
      | Backup, Cmd i => let log' := log s ++ [i] in
                        let (_, db') := execute i (db s) in
                        (serialize (Data db' log' (nextIndex s)),
                         [(Primary, serialize Ack)],
                         [])
      | _, _ => nop (serialize s)
      end
      end
      end.

    Definition initial_data : data := Data [] [] 0.

    Definition upgrade (_ : bytes) : option bytes := Some (serialize initial_data).

    Definition version : Top.version name := Version handleInput handleMsg.
    Definition versions := [(upgrade, version)].

    Section Serializer.
      Variable A : Type.
      Context {sA : Serializer A}.
      Variable P : A -> Prop.

      Definition lift_strict (b : bytes) : Prop :=
        match deserialize b with
        | None => False
        | Some (a,_) => P a
        end.

      Definition lift (b : bytes) : Prop :=
        match deserialize b with
        | None => True
        | Some (a,_) => P a
        end.

      Lemma Serialize_reversible' :
        forall a, deserialize (serialize a) = Some (a, []).
      Proof.
        intros.
        rewrite <- app_nil_r with (l := serialize a).
        now rewrite Serialize_reversible.
      Qed.

      Lemma lift_strict_of_serialize :
        forall a,
          P a ->
          lift_strict (serialize a).
      Proof.
        unfold lift_strict.
        intros.
        now rewrite Serialize_reversible'.
      Qed.

      Lemma lift_strict_of_deserialize_some :
        forall a b rest,
          deserialize b = Some (a, rest) ->
          P a ->
          lift_strict b.
      Proof.
        unfold lift_strict.
        intros.
        now find_rewrite.
      Qed.

      Lemma lift_strict_not_None :
        forall b,
          deserialize b = None ->
          lift_strict b ->
          False.
      Proof.
        unfold lift_strict.
        intros.
        find_rewrite.
        auto.
      Qed.
    End Serializer.

    Lemma lift_strict_None :
      forall A (sA : Serializer A) b1 b2,
        lift_strict (fun _ => True) b1 <-> lift_strict (fun _ => True) b2 ->
        deserialize b1 = None ->
        deserialize b2 = None.
    Proof.
      unfold lift_strict.
      intros.
      repeat break_match; intuition; subst.
      discriminate.
    Qed.

    Lemma nop_no_msgs :
      forall s st ms os,
        nop s = (st, ms, os) -> ms = [].
    Proof. unfold nop. congruence. Qed.

    Lemma nop_state :
      forall s st ms os,
        nop s = (st, ms, os) -> st = s.
    Proof. unfold nop. congruence. Qed.

    Lemma nop_elim :
      forall s st ms os,
        nop s = (st, ms, os) -> st = s /\ ms = [] /\ os = [].
    Proof. unfold nop. intuition congruence. Qed.



    Lemma only_one_version :
      forall n u v,
        nth_error versions n = Some (u, v) ->
        u = upgrade /\ v = version /\ n = 0.
    Proof.
      unfold versions.
      intros.
      destruct n; simpl in *.
      - find_inversion. auto.
      - destruct n; simpl in *; discriminate.
    Qed.

    Section Forall.
      Variable A : Type.
      Variable P : A -> Prop.

      Lemma Forall_app_intro :
        forall xs ys,
          Forall P xs ->
          Forall P ys ->
          Forall P (xs ++ ys).
      Proof.
        induction 1; simpl; auto.
      Qed.

      Lemma Forall_middle_elim :
        forall xs y zs,
          Forall P (xs ++ y :: zs) ->
          Forall P (xs ++ zs).
      Proof.
        induction xs; simpl; intros; invc H; eauto.
      Qed.
    End Forall.

    Lemma handleMsg_all_packets_deserialize :
      forall h m st st' ms os,
        handleMsg h m st = (st', ms, os) ->
        Forall (fun p => lift_strict (fun _ : msg => True) (snd p)) ms.
    Proof.
      unfold handleMsg.
      intros.
      repeat break_match;
          try solve [find_apply_lem_hyp nop_no_msgs; repeat find_rewrite; auto];
        find_inversion; auto.
      - constructor; simpl; auto using lift_strict_of_serialize.
      - constructor; simpl; auto using lift_strict_of_serialize.
    Qed.

    Lemma handleMsg_version :
      Top.handleMsg version = handleMsg.
    Proof.
      reflexivity.
    Qed.

    Lemma handleInput_version :
      Top.handleInput version = handleInput.
    Proof.
      reflexivity.
    Qed.

    Lemma handleInput_all_packets_deserialize :
      forall h i st st' ms os,
        handleInput h i st = (st', ms, os) ->
        Forall (fun p => lift_strict (fun _ : msg => True) (snd p)) ms.
    Proof.
      unfold handleInput.
      intros.
      intros.
      repeat break_match;
          try solve [find_apply_lem_hyp nop_no_msgs; repeat find_rewrite; auto];
        find_inversion; auto.
      constructor; simpl; auto using lift_strict_of_serialize.
    Qed.

    Lemma all_packets_deserialize :
      forall w,
        step_reachable versions w ->
        Forall (fun p => lift_strict (fun _ : msg => True) (snd p)) (packets w).
    Proof.
      induction 1; intros.
      - unfold initial_world in *. simpl in *. constructor.
      - clear H0. invcs H.
        + auto.
        + repeat find_rewrite.
          apply Forall_app_intro.
          * find_apply_lem_hyp only_one_version.
            break_and. subst.
            rewrite handleMsg_version in *.
            eauto using handleMsg_all_packets_deserialize.
          * eauto using Forall_middle_elim.
        + apply Forall_app_intro.
          * find_apply_lem_hyp only_one_version.
            break_and. subst.
            rewrite handleInput_version in *.
            eauto using handleInput_all_packets_deserialize.
          * eauto using Forall_middle_elim.
    Qed.

    Lemma upgrade_deserializes :
      forall st st',
        upgrade st = Some st' ->
        lift_strict (fun _ => True) st'.
    Proof.
      unfold upgrade.
      intros.
      find_inversion.
      auto using lift_strict_of_serialize.
    Qed.

    Lemma handleMsg_deserializes_None_eq :
      forall h m st st' ms os,
        handleMsg h m st = (st', ms, os) ->
        deserialize st' = None ->
        st' = st.
    Proof.
      unfold handleMsg.
      intros.
      repeat break_match; repeat find_inversion;
      try find_apply_lem_hyp nop_state; subst;
      try (rewrite Serialize_reversible' in *; discriminate).
      auto.
    Qed.

    Lemma handleInput_deserializes_None_eq :
      forall h m st st' ms os,
        handleInput h m st = (st', ms, os) ->
        deserialize st' = None ->
        st' = st.
    Proof.
      unfold handleInput.
      intros.
      repeat break_match; repeat find_inversion;
      try find_apply_lem_hyp nop_state; subst;
      try (rewrite Serialize_reversible' in *; discriminate).
      auto.
    Qed.

    Ltac update_rewrite := rewrite ?@update_same in *; rewrite ?@update_neq in * by congruence.

    Lemma initialized_state_deserializes :
      forall w,
        step_reachable versions w ->
        (forall h,
            deserialize (localState w h) = None ->
            nextVersion w h = 0 /\ localState w h = []).
    Proof.
      induction 1; intros.
      - simpl. auto.
      - clear H0. invcs H; find_apply_lem_hyp only_one_version; break_and; subst.
        + destruct (eq_dec h0 h); subst; update_rewrite.
          * find_apply_lem_hyp upgrade_deserializes.
            exfalso. eauto using lift_strict_not_None.
          * find_apply_hyp_hyp.
            auto.
        + rewrite handleMsg_version in *.
          destruct (eq_dec h h0); subst; update_rewrite.
          * find_apply_lem_hyp handleMsg_deserializes_None_eq; subst; auto.
          * auto.
        + rewrite handleInput_version in *.
          destruct (eq_dec h h0); subst; update_rewrite.
          * find_apply_lem_hyp handleInput_deserializes_None_eq; subst; auto.
          * auto.
    Qed.

    Lemma version_0_is_init :
      forall w,
        step_reachable versions w ->
        (forall h,
            nextVersion w h = 0 -> localState w h = []).
    Proof.
      induction 1; intros.
      - auto.
      - clear H0. invcs H; find_apply_lem_hyp only_one_version; break_and; subst.
        + destruct (eq_dec h h0); subst; update_rewrite; try discriminate.
          auto.
        + assert (h <> h0) by congruence.
          update_rewrite. auto.
        + assert (h <> h0) by congruence.
          update_rewrite. auto.
    Qed.

    Definition backup_prefix (w : world name) : Prop :=
      match deserialize (localState w Backup) with
      | None => True
      | Some (backup, _) =>
      match deserialize (localState w Primary) with
      | None => True
      | Some (primary, _) =>
      Prefix (log backup) (log primary)
      end
      end.

    Definition get_log (b : bytes) : list input :=
      match deserialize b with
      | None => []
      | Some (d, _) => log d
      end.

    Fixpoint take_strict {A} (n : nat) (l : list A) : option (list A) :=
      match n with
      | 0 => Some []
      | S n' => match l with
               | [] => None
               | x :: l' => match take_strict n' l' with None => None
                           | Some l'' => Some (x :: l'')
                           end
               end
      end.

    Lemma take_strict_length :
      forall A n (l : list A) l',
        take_strict n l = Some l' ->
        length l' = n.
    Proof.
      induction n; simpl; intros.
      - find_inversion. auto.
      - repeat break_match; try discriminate.
        find_inversion. simpl. eauto.
    Qed.


    Definition I (w : world name) : Prop :=
      match deserialize (localState w Primary) with
      | None => packets w = [] /\ get_log (localState w Backup) = []
      | Some (primary, _) =>
        (packets w = [] /\
         take_strict (nextIndex primary) (log primary) = Some (get_log (localState w Backup))) \/
        (exists i, packets w = [(Backup, serialize (Cmd i))] /\
              take_strict (S (nextIndex primary)) (log primary) =
                  Some (get_log (localState w Backup) ++ [i])) \/
        (packets w = [(Primary, serialize Ack)] /\
         take_strict (S (nextIndex primary)) (log primary) = Some (get_log (localState w Backup)))
      end.

    Lemma deserialize_data_nil :
      deserialize [] = @None (data * _).
    Proof.
      auto.
    Qed.

    Lemma get_log_initialize :
      get_log [] = get_log (serialize initial_data).
    Proof. auto. Qed.

    Lemma take_strict_lt_None :
      forall A n (l : list A),
        length l < n ->
        take_strict n l = None.
    Proof.
      induction n; destruct l; simpl; intros.
      - omega.
      - omega.
      - auto.
      - now rewrite IHn by omega.
    Qed.

    Lemma take_strict_unroll :
      forall A n (l : list A),
        take_strict (S n) l = match l with
                              | [] => None
                              | x :: l' => match take_strict n l' with None => None
                                          | Some l'' => Some (x :: l'')
                                          end
                              end.
    Proof. auto. Qed.

    Lemma take_strict_nth_error_Some :
      forall A n (l : list A) l' a,
        take_strict n l = Some l' ->
        nth_error l n = Some a ->
        take_strict (S n) l = Some (l' ++ [a]).
    Proof.
      induction n; intros.
      - simpl in *. find_inversion. simpl. break_match; congruence.
      - rewrite take_strict_unroll in *.
        cbn [nth_error] in *.
        break_match; try discriminate.
        break_match_hyp.
        + find_inversion.
          erewrite IHn; eauto.
          auto.
        + discriminate.
    Qed.

    Lemma take_strict_length_exact :
      forall A (l : list A) x,
        length l = x ->
        take_strict x l = Some l.
    Proof.
      induction l; intros; subst; simpl in *; auto.
      rewrite IHl; auto.
    Qed.

    Lemma take_strict_app :
      forall A (l : list A) x l' l'',
        take_strict x l = Some l' ->
        take_strict x (l ++ l'') = Some l'.
    Proof.
      induction l; intros; subst; simpl in *; auto.
      - destruct x; simpl in *; auto. discriminate.
      - destruct x; simpl in *; auto.
        break_match_hyp; try discriminate.
        erewrite IHl; eauto.
    Qed.

    Lemma take_strict_Prefix :
      forall A x (l : list A) l',
        take_strict x l = Some l' ->
        Prefix l' l.
    Proof.
      induction x; intros; simpl in *; auto.
      - find_inversion. constructor.
      - repeat break_match; try discriminate.
        find_inversion.
        constructor; auto.
    Qed.

    Lemma take_strict_S_snoc :
      forall A x (l : list A) l' a,
        take_strict (S x) l = Some (l' ++ [a]) ->
        take_strict x l = Some l'.
    Proof.
      induction x; intros; rewrite take_strict_unroll in *;
          destruct l; try discriminate.
      - destruct l'; auto.
        destruct l'; discriminate.
      - break_match_hyp; try discriminate.
        destruct l'; cbn [app] in *; find_inversion.
        + find_apply_lem_hyp take_strict_length. cbn [length] in *. omega.
        + now erewrite IHx by eauto.
    Qed.
    
    Local Arguments nth_error : simpl never.
    Local Arguments take_strict : simpl never.
    Lemma get_log_serialize :
      forall x,
        get_log (serialize x) = log x.
    Proof.
      intros.
      unfold get_log.
      rewrite Serialize_reversible'; auto.
    Qed.

    Lemma I_packet_to_primary_elim :
      forall w mb, I w ->
              In (Primary, mb) (packets w) ->
              deserialize mb = Some (Ack, []) /\
              packets w = [(Primary, mb)] /\
              exists primary rest,
                deserialize (localState w Primary) = Some (primary, rest) /\
                take_strict (S (nextIndex primary)) (log primary) =
                Some (get_log (localState w Backup)).
    Proof.
      unfold I.
      intros.
      repeat break_match; repeat break_or_hyp; break_exists; break_and; subst;
        repeat find_rewrite; simpl in *; repeat break_or_hyp; intuition; find_inversion; eauto.
    Qed.

    Lemma I_packet_to_backup_elim :
      forall w mb, I w ->
              In (Backup, mb) (packets w) ->
              (exists i, deserialize mb = Some (Cmd i, []) /\
                    packets w = [(Backup, mb)] /\
                    exists primary rest,
                      deserialize (localState w Primary) = Some (primary, rest) /\
                      take_strict (S (nextIndex primary)) (log primary) =
                      Some (get_log (localState w Backup) ++ [i])).
    Proof.
      unfold I.
      intros.
      repeat break_match; repeat break_or_hyp; break_exists; break_and; subst;
        repeat find_rewrite; simpl in *; repeat break_or_hyp; intuition; find_inversion; eauto.
      rewrite Serialize_reversible'. eauto 10.
    Qed.

    Lemma get_log_deserialize_Some :
      forall s d rest,
        deserialize s = Some (d, rest) ->
        get_log s = log d.
    Proof.
      unfold get_log.
      intros.
      now find_rewrite.
    Qed.

    Lemma I_true :
      forall w,
        step_reachable versions w ->
        I w.
    Proof.
      induction 1 using step_reachable_ind.
      - unfold I, initial_world. simpl. auto.
      - invcs H0.
        + (* upgrade case *)
          find_apply_lem_hyp only_one_version.
          break_and. subst.
          unfold I in *. simpl in *.
          unfold upgrade in *. find_inversion.
          destruct h; subst; update_rewrite.
          * (* Primary *)
            rewrite Serialize_reversible'.
            simpl in *.
            rewrite version_0_is_init in * by auto.
            rewrite deserialize_data_nil in *.
            unfold take_strict.
            intuition congruence.
          * (* Backup *)
            rewrite version_0_is_init with (h := Backup) in * by auto.
            now rewrite get_log_initialize in *.
        + (* msg case *)
          find_apply_lem_hyp only_one_version.
          break_and. subst.
          rewrite handleMsg_version in *.
          unfold handleMsg in *. simpl in *.
          break_match_hyp; [| find_apply_lem_hyp initialized_state_deserializes; auto; omega].
          break_let. subst.
          break_match_hyp.
          * break_let. subst.
            break_match_hyp; subst; update_rewrite.
            -- (* Primary *)
              find_eapply_lem_hyp I_packet_to_primary_elim; [|repeat find_rewrite; eauto with *].
              break_and. break_exists. break_and.
              repeat find_rewrite. repeat find_inversion.
              ++ unfold I. simpl. update_rewrite.
                 destruct xs; [|destruct xs; discriminate].
                 cbn [app] in *. find_inversion.
                 break_match_hyp.
                 ** break_let. find_inversion.
                    rewrite Serialize_reversible'.
                    simpl in *.
                    break_match; auto.
                    rewrite app_nil_r.
                    intuition eauto using take_strict_nth_error_Some.
                 ** find_apply_lem_hyp nop_elim. break_and. subst.
                    exfalso.
                    find_apply_lem_hyp nth_error_None.
                    rewrite take_strict_lt_None in * by omega.
                    discriminate.
            -- (* Backup *)
              find_eapply_lem_hyp I_packet_to_backup_elim; [|eauto with *].
              break_exists. break_and. break_exists. break_and.
              repeat find_rewrite. repeat find_inversion.
              break_let. find_inversion.
              destruct xs; [|destruct xs; discriminate].
              cbn [app] in *. find_inversion.
              unfold I. simpl. update_rewrite. repeat find_rewrite.
              right. right.
              rewrite get_log_serialize. simpl.
              erewrite get_log_deserialize_Some by eauto.
              auto.
          * find_apply_lem_hyp all_packets_deserialize.
            exfalso.
            find_eapply_lem_hyp Forall_forall; [|eauto with *].
            simpl in *.
            eapply lift_strict_not_None with (A := msg); eauto.
        + (* handleInput *)
          find_apply_lem_hyp only_one_version.
          break_and. subst.
          rewrite handleInput_version in *.
          unfold I, handleInput in *. simpl in *.
          break_match_hyp; [| find_apply_lem_hyp initialized_state_deserializes; auto; omega].
          break_let. subst.
          break_match_hyp.
          * break_let. break_match_hyp; subst.
            -- repeat find_rewrite.
               update_rewrite.
               find_inversion.
               rewrite Serialize_reversible'. simpl.
               break_if; simpl.
               ++ right. left.
                  intuition.
                  ** repeat find_rewrite. eexists; intuition eauto.
                     rewrite take_strict_length_exact in *; auto; [congruence|].
                     rewrite app_length. simpl. omega.
                  ** exfalso.
                     break_exists. break_and.
                     erewrite take_strict_lt_None in *; try discriminate. omega.
                  ** exfalso. erewrite take_strict_lt_None in *; try discriminate. omega.
               ++ repeat break_or_hyp.
                  ** left.
                     break_and.
                     erewrite take_strict_app; eauto.
                  ** right. left.
                     break_exists; break_and.
                     erewrite take_strict_app; eauto.
                  ** right. right.
                     break_and.
                     erewrite take_strict_app; eauto.
            -- find_apply_lem_hyp nop_elim.
               break_and; subst. simpl in *.
               update_rewrite.
               unfold get_log in *.
               repeat find_rewrite.
               rewrite Serialize_reversible'. auto.
          * find_apply_lem_hyp nop_elim.
            break_and; subst. simpl in *.
            destruct h; update_rewrite; repeat find_rewrite;
              try rewrite Serialize_reversible'; auto.
            unfold get_log in *.
            repeat find_rewrite.
            rewrite Serialize_reversible'. auto.
    Qed.


    Theorem backup_prefix_true :
      forall w,
        step_reachable versions w ->
        backup_prefix w.
    Proof.
      intros.
      find_apply_lem_hyp I_true.
      unfold I, backup_prefix in *.
      repeat break_match; auto.
      unfold get_log in *. repeat find_rewrite.
      intuition eauto using take_strict_Prefix.
      - break_exists. intuition.
        find_apply_lem_hyp take_strict_S_snoc.
        eauto using take_strict_Prefix.
    Qed.
  End VersionOne.


  Module VersionTwo.
    Inductive input := Put (k v : string) | Get (k : string) | Append (k s : string).
    Definition input_serialize (i : input) : bytes :=
      serialize 1 ++
      match i with
      | Put k v => serialize 0 ++ serialize k ++ serialize v
      | Get k => serialize 1 ++ serialize k
      | Append k s => serialize 2 ++ serialize k ++ serialize s
      end.
    Definition input_deserialize (bs : bytes) : option (input * bytes) :=
      match deserialize bs with None => None
      | Some (ver, rest) =>
        if Nat.eq_dec ver 1
        then
          match deserialize rest with None => None
          | Some (tag, rest) =>
          match deserialize rest with None => None
          | Some (k, rest) =>
              match tag with
              | 0 =>
                match deserialize rest with None => None
                | Some (v,rest) => Some (Put k v, rest)
                end
              | 1 => Some (Get k, rest)
              | 2 =>
                match deserialize rest with None => None
                | Some (s,rest) => Some (Append k s, rest)
                end
              | _ => None
              end
          end
          end
        else None
      end.
    Instance input_Serializer : Serializer input :=
      {| serialize := input_serialize;
         deserialize := input_deserialize
      |}.
    unfold input_serialize, input_deserialize.
    intros.
    destruct x;
       rewrite !app_assoc_reverse;
       now rewrite !Serialize_reversible.
    Defined.

    Inductive msg := Cmd (i : input) | Ack.
    Definition msg_serialize (m : msg) : bytes :=
      serialize 0 ++
      match m with
      | Cmd i => serialize true ++ serialize i
      | Ack => serialize false
      end.
    Definition msg_deserialize (bs : bytes) : option (msg * bytes) :=
        match deserialize bs with None => None
        | Some (ver, rest)  =>
        match deserialize rest with None => None
        | Some (b, rest) =>
          if Nat.eq_dec ver 0
          then if b:bool
               then match deserialize rest with None => None
                                           | Some (i, rest) => Some (Cmd i, rest)
                    end
               else Some (Ack, rest)
          else None
        end
        end.
    Instance msg_Serializer : Serializer msg :=
      {| serialize := msg_serialize;
         deserialize := msg_deserialize
      |}.
    unfold msg_serialize, msg_deserialize.
    intros.
    destruct x;
      rewrite !app_assoc_reverse;
      now rewrite !Serialize_reversible.
    Defined.

    Inductive output := ResGet (k v : string)
                      | ResPut (k old_v v : string)
                      | ResAppend (k s old_v v : string).
    Definition output_serialize (o : output) : bytes :=
      serialize 1 ++
      match o with
      | ResGet k v => serialize 0 ++ serialize k ++ serialize v
      | ResPut k old_v v => serialize 1 ++ serialize k ++ serialize old_v ++ serialize v
      | ResAppend k s old_v v => serialize 2 ++ serialize k ++ serialize s ++
                                serialize old_v ++ serialize v
      end.
    Definition output_deserialize (bs : bytes) : option (output * bytes) :=
      match deserialize bs with None => None
      | Some (ver, rest) =>
        if Nat.eq_dec ver 1
        then
          match deserialize rest with None => None
          | Some (tag, rest) =>
            match deserialize rest with None => None
            | Some (k, rest) =>
            match tag with
            | 0 =>
              match deserialize rest with None => None
              | Some (v, rest) => Some (ResGet k v, rest)
              end
            | 1 =>
              match deserialize rest with None => None
              | Some (old_v, rest) =>
              match deserialize rest with None => None
              | Some (v, rest) => Some (ResPut k old_v v, rest)
              end
              end
            | 2 =>
              match deserialize rest with None => None
              | Some (s, rest) =>
              match deserialize rest with None => None
              | Some (old_v, rest) =>
              match deserialize rest with None => None
              | Some (v, rest) => Some (ResAppend k s old_v v, rest)
              end
              end
              end
            | _ => None
            end
            end
          end
        else None
      end.
    Instance output_Serializer : Serializer output :=
      {| serialize := output_serialize;
         deserialize := output_deserialize
      |}.
    unfold output_serialize, output_deserialize.
    intros.
    destruct x;
      rewrite !app_assoc_reverse;
      now rewrite !Serialize_reversible.
    Defined.

    Record data := Data { db : list (string * string);
                          log : list input;
                          nextIndex : nat
                        }.
    Definition data_serialize (d : data) : bytes :=
      serialize (db d) ++ serialize (log d) ++ serialize (nextIndex d).
    Definition data_deserialize (bs : bytes) : option (data * bytes) :=
      match deserialize bs with None => None
      | Some (db, rest) =>
      match deserialize rest with None => None
      | Some (log, rest) =>
      match deserialize rest with None => None
      | Some (ni, rest) => Some (Data db log ni, rest)
      end
      end
      end.
    Instance data_Serializer : Serializer data :=
      {| serialize := data_serialize;
         deserialize := data_deserialize
      |}.
    unfold data_serialize, data_deserialize.
    intros.
    destruct x.
    rewrite !app_assoc_reverse.
    now rewrite !Serialize_reversible.
    Defined.

    Definition nop (s : bytes) : bytes * list (name * bytes) * list bytes := (s, [], []).

    Definition handleInput (n : name) (i : bytes) (s : bytes) :
        bytes * list (name * bytes) * list bytes :=
      match deserialize s with None => nop s
      | Some (s, _) =>
      match deserialize i with None => nop (serialize s)
      | Some (i, _) =>
      match n with
      | Primary =>
        let log' := log s ++ [i] in
        let ms := if Nat.eq_dec (length (log s)) (nextIndex s)
                  then [(Backup, serialize (Cmd i))]
                  else [] in
        (serialize (Data (db s) log' (nextIndex s)), ms, [])
      | Backup => nop (serialize s)
      end
      end
      end.

    Definition execute (i : input) (db : list (string * string))
        : output * list (string * string) :=
      match i with
      | Put k v => let old_v := assoc_default String.string_dec db String.EmptyString k in
                  let db' := assoc_set String.string_dec db k v in
                  (ResPut k old_v v, db')
      | Get k => let v := assoc_default String.string_dec db String.EmptyString k in
                (ResGet k v, db)
      | Append k s => let old_v := assoc_default String.string_dec db String.EmptyString k in
                     let v := String.append old_v s in
                     let db' := assoc_set String.string_dec db k v in
                     (ResAppend k s old_v v, db')
      end.

    Definition handleMsg (n : name) (m : bytes) (s : bytes) :
        bytes * list (name * bytes) * list bytes :=
      match deserialize s with None => nop s
      | Some (s, _) =>
      match deserialize m with None => nop (serialize s)
      | Some (m, _) =>
      match n, m with
      | Primary, Ack =>
        match nth_error (log s) (nextIndex s) with None => nop (serialize s)
        | Some i => let (o, db') := execute i (db s) in
                   let ni' := S (nextIndex s) in
                   let ms := match nth_error (log s) ni' with
                             | None => []
                             | Some i' => [(Backup, serialize (Cmd i))]
                             end
                   in (serialize (Data db' (log s) ni'), ms, [serialize o])
        end
      | Backup, Cmd i => let log' := log s ++ [i] in
                        let (_, db') := execute i (db s) in
                        (serialize (Data db' log' (nextIndex s)),
                         [(Primary, serialize Ack)],
                         [])
      | _, _ => nop (serialize s)
      end
      end
      end.

    Definition upgrade_input (i : VersionOne.input) : VersionTwo.input :=
      match i with
      | VersionOne.Put k v => VersionTwo.Put k v
      | VersionOne.Get k => VersionTwo.Get k
      end.

    Definition upgrade_data (d : VersionOne.data) : VersionTwo.data :=
      VersionTwo.Data (VersionOne.db d)
                      (map upgrade_input (VersionOne.log d))
                      (VersionOne.nextIndex d).

    Definition upgrade (b : bytes) : option bytes :=
      match deserialize b with None => None
      | Some (d, _) => Some (serialize (upgrade_data d))
      end.

    Definition version : Top.version name := Version handleInput handleMsg.
    Definition versions := VersionOne.versions ++ [(upgrade, version)].
  End VersionTwo.
End PBKV.