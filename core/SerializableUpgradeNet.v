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

    Definition initial_data : data := Data [] [] 0.

    Definition upgrade (_ : bytes) : option bytes := Some (serialize initial_data).

    Definition version : Top.version name := Version handleInput handleMsg.
    Definition versions := [(upgrade, version)].

    Definition backup_prefix (w : world name) : Prop :=
      match deserialize (localState w Backup) with
      | None => nextVersion w Backup = 0 /\ localState w Backup = []
      | Some (backup, _) =>
      match deserialize (localState w Primary) with
      | None => nextVersion w Primary = 0 /\ localState w Primary = []
      | Some (primary, _) =>
      Prefix (log backup) (log primary)
      end
      end.

    Definition serialize_packet_invariant (P : name -> msg -> Prop) (p : name * bytes) : Prop :=
      let (dst, m) := p in
      match deserialize m with
      | None => False
      | Some (m,_) => P dst m
      end.
    Definition backup_network_prefix (w : world name) : Prop :=
      match deserialize (localState w Backup) with
      | None => nextVersion w Backup = 0 /\ localState w Backup = []
      | Some (backup, _) =>
      match deserialize (localState w Primary) with
      | None => nextVersion w Primary = 0 /\ localState w Primary = []
      | Some (primary, _) =>
        (exists dst m,
         packets w = [(dst, m)] /\
         match deserialize m with None => False
         | Some (m, _) =>
         match m with
         | Cmd i => Prefix (log backup ++ [i]) (log primary)
         | Ack => Prefix (log backup) (log primary)
         end
         end) \/ (packets w = [] /\ Prefix (log backup) (log primary))
      end
      end.
    Lemma Serialize_reversible' A {sA : Serializer A} :
      forall a, deserialize (serialize a) = Some (a, []).
    Proof.
      intros.
      rewrite <- app_nil_r with (l := serialize a).
      now rewrite Serialize_reversible.
    Qed.

    Lemma nop_no_msgs :
      forall s st ms os,
        nop s = (st, ms, os) -> ms = [].
    Proof. unfold nop. congruence. Qed.

    Lemma only_one_version :
      forall n u v,
        nth_error versions n = Some (u, v) ->
        u = upgrade /\ v = version.
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

    Lemma serialize_packet_invariant_of_serialize:
      forall (P : _ -> _ -> Prop) h m,
        P h m ->
        serialize_packet_invariant P (h, serialize m).
    Proof.
      unfold serialize_packet_invariant.
      intros.
      now rewrite Serialize_reversible'.
    Qed.

    Lemma handleMsg_all_packets_deserialize :
      forall h m st st' ms os,
        handleMsg h m st = (st', ms, os) ->
        Forall (serialize_packet_invariant (fun _ _ => True)) ms.
    Proof.
      unfold handleMsg.
      intros.
      repeat break_match;
          try solve [find_apply_lem_hyp nop_no_msgs; repeat find_rewrite; auto];
        find_inversion; auto using serialize_packet_invariant_of_serialize.
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
        Forall (serialize_packet_invariant (fun _ _ => True)) ms.
    Proof.
      unfold handleInput.
      intros.
      intros.
      repeat break_match;
          try solve [find_apply_lem_hyp nop_no_msgs; repeat find_rewrite; auto];
        find_inversion; auto using serialize_packet_invariant_of_serialize.
    Qed.

    Lemma all_packets_deserialize :
      forall w,
        step_reachable versions w ->
        Forall (serialize_packet_invariant (fun _ _ => True)) (packets w).
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

    Lemma backup_network_prefix_true :
      forall w,
        step_reachable versions w ->
        backup_network_prefix w.
    Proof.
    Admitted.

    Theorem backup_prefix_true :
      forall w,
        step_reachable versions w ->
        backup_prefix w.
    Proof.
      intros w Hreach.
      pose proof backup_network_prefix_true Hreach.
      unfold backup_network_prefix, backup_prefix in *.
      repeat break_match; intuition; subst.
      break_exists_name dst.
      break_exists_name m.
      break_and.
      repeat break_match; intuition.
      find_apply_lem_hyp Prefix_elim.
      break_exists.
      find_rewrite.
      rewrite app_assoc_reverse.
      eauto using app_Prefix.
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