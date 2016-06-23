(* Trick for recons: nothing to do with CO-induction *)

Lemma recons_surj_pair : forall A B (x: A * B), x = (fst x, snd x).
intros A B x. simpl (* no progress *).  
(* Trick : you have to eat x first *)
case x.  simpl. reflexivity.
Qed.

Lemma recons_nat : 
  forall n, (match n with O => 1 = 0 | _ => True end) -> S (pred n) = n. 
intro n; case n; clear n; simpl.
  trivial. 
  reflexivity. 
Qed.



(* ------------------------------------------------------------------------- *)

(* General tactics *)


Ltac genclear H := generalize H; clear H.

Ltac clearall :=
   repeat
        match goal with [H : _ |- _ ] => clear H end
     || match goal with [H : _ |- _ ] => genclear H end. 

(* ------------------------------------------------------------------------- *)
(* Infinite traces *)
Definition infseq_nat (T:Type) := nat -> T.

Section sec_infseq.
Variable T: Type. 

CoInductive infseq : Type := Cons : T -> infseq -> infseq.

Definition hd (s:infseq) : T := match s with Cons x _ => x end.

Definition tl (s:infseq) : infseq := match s with Cons _ s => s end.

Lemma recons : forall s, Cons (hd s) (tl s) = s.
intros s. 
(* Trick : simpl doesn't progress, you have to eat s first *)
case s.  simpl. reflexivity.
Qed.

End sec_infseq.

Implicit Arguments Cons [T].
Implicit Arguments hd [T].
Implicit Arguments tl [T].
Implicit Arguments recons [T].

CoInductive emb_infprops : infseq Prop -> Prop := 
  EMB : forall (P:Prop) s, P -> emb_infprops s -> emb_infprops (Cons P s).




(* ------------------------------------------------------------------------- *)
(* Extensional equality on infinite sequences *)
Section sec_exteq.

Variable T: Type. 

CoInductive exteq_infseq : infseq T -> infseq T -> Prop :=
  exteq_infseq_intro :
    forall x s1 s2, exteq_infseq s1 s2 -> exteq_infseq (Cons x s1) (Cons x s2).

Lemma exteq_infseq_inversion :
  forall (x1:T) s1 x2 s2, 
  exteq_infseq (Cons x1 s1) (Cons x2 s2) -> x1 = x2 /\ exteq_infseq s1 s2.
Proof.
intros x1 s1 x2 s2 e. 
change (hd (Cons x1 s1) = hd (Cons x2 s2) /\
        exteq_infseq (tl (Cons x1 s1)) (tl (Cons x2 s2))).
case e; clear e x1 s1 x2 s2. simpl. intros; split; trivial. 
Qed.

Lemma exteq_refl : forall s, exteq_infseq s s. 
Proof.
cofix cf. intros (x, s). constructor. apply cf. 
Qed.

Lemma exteq_sym : forall s1 s2, exteq_infseq s1 s2 -> exteq_infseq s2 s1.
Proof.
cofix cf. destruct 1. constructor. apply cf. assumption. 
Qed.

Lemma exteq_trans :
   forall s1 s2 s3, exteq_infseq s1 s2 -> exteq_infseq s2 s3 -> exteq_infseq s1 s3.
Proof.
cofix cf.
intros (x1, s1) (x2, s2) (x3, s3) e12 e23. 
case (exteq_infseq_inversion _ _ _ _ e12); clear e12; intros e12 ex12. 
case (exteq_infseq_inversion _ _ _ _ e23); clear e23; intros e23 ex23. 
rewrite e12; rewrite e23. constructor. apply cf with s2; assumption. 
Qed.

End sec_exteq.

Implicit Arguments exteq_infseq [T]. 
Implicit Arguments exteq_infseq_inversion [T x1 s1 x2 s2]. 
Implicit Arguments exteq_refl [T]. 
Implicit Arguments exteq_sym [T]. 
Implicit Arguments exteq_trans [T]. 




(* --------------------------------------------------------------------------- *)
(* Zipping two infseqs: useful for Map theory *)
Section sec_zip.

Variable A B: Type.

CoFixpoint zip (sA: infseq A) (sB: infseq B) : infseq (A*B) := 
  match sA, sB with
    | Cons a sA0, Cons b sB0 => Cons (a, b) (zip sA0 sB0)
  end.

Lemma zip_Cons: forall (a:A) (b:B) sA sB, zip (Cons a sA) (Cons b sB) = Cons (a, b) (zip sA sB). 
Proof.
intros. pattern (zip (Cons a sA) (Cons b sB)); rewrite <- recons. simpl. reflexivity. 
Qed.

End sec_zip.

Implicit Arguments zip [A B].
Implicit Arguments zip_Cons [A B].


(* Map *)
Section sec_map.

Variable A B: Type.

CoFixpoint Map (f: A->B) (s: infseq A): infseq B :=
  match s with
   Cons x s => Cons (f x) (Map f s)
  end.

Lemma Map_Cons: forall (f:A->B) x s, Map f (Cons x s) = Cons (f x) (Map f s).
intros. pattern (Map f (Cons x s)). rewrite <- recons. simpl. reflexivity.
Qed.

End sec_map. 
Implicit Arguments Map [A B].
Implicit Arguments Map_Cons [A B].



(* --------------------------------------------------------------------------- *)
(* Temporal logic operations *)

Section sec_modal_op_defn.

Variable T : Type.

Definition now (P: T->Prop) (s: infseq T) : Prop :=
  match s with Cons x s => P x end.

Definition next (P: infseq T -> Prop) (s: infseq T) : Prop :=
  match s with Cons x s => P s end.

Definition consecutive  (R: T -> T -> Prop) (s: infseq T) : Prop :=
  match s with Cons x1 (Cons x2 s) => R x1 x2 end. 

CoInductive always1 (P: T->Prop) : infseq T -> Prop :=
  | Always1 : forall x s, P x -> always1 P s -> always1 P (Cons x s).

CoInductive always (P: infseq T->Prop) : infseq T -> Prop :=
  | Always : forall s, P s -> always P (tl s) -> always P s.

CoInductive until (J P: infseq T->Prop) : infseq T -> Prop :=
  | Until0 : forall s, P s -> until J P s
  | Until_tl : forall s, J s -> until J P (tl s) -> until J P s.

Inductive eventually (P: infseq T->Prop) : infseq T -> Prop :=
  | E0 : forall s, P s -> eventually P s
  | E_next : forall x s, eventually P s -> eventually P (Cons x s). 

Definition inf_often (P: infseq T->Prop) (s: infseq T) : Prop :=
  always (eventually P) s.

Definition continuously (P: infseq T->Prop) (s: infseq T) : Prop :=  
  eventually (always P) s.

(* temporal logic connectors *)
Definition impl_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s -> Q s. 
Definition and_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s /\ Q s. 
Definition or_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s \/ Q s. 
Definition not_tl (P : infseq T -> Prop) : infseq T -> Prop := 
  fun s => ~ P s.

End sec_modal_op_defn.

Implicit Arguments now [T].
Implicit Arguments next [T].
Implicit Arguments consecutive [T].
Implicit Arguments always [T].
Implicit Arguments always1 [T].
Implicit Arguments eventually [T].
Implicit Arguments until [T].
Implicit Arguments inf_often [T].
Implicit Arguments continuously [T].

Implicit Arguments impl_tl [T].
Implicit Arguments and_tl [T].
Implicit Arguments or_tl [T].
Implicit Arguments not_tl [T].

Notation "A ->_ B" := (impl_tl A B) (right associativity, at level 90).
Notation "A /\_ B" := (and_tl A B) (right associativity, at level 80).
Notation "A \/_ B" := (or_tl A B) (right associativity, at level 85).
Notation "~_ A" := (not_tl A) (right associativity, at level 90).


(* *)


Section sec_modal_op_lemmas.

Variable T : Type.

Lemma always_Cons :
  forall (x: T) (s: infseq T) P,
  always P (Cons x s) -> P (Cons x s) /\ always P s.
Proof.
intros x s P al. change (P (Cons x s) /\ always P (tl (Cons x s))). 
destruct al. split; assumption.
Qed.

Lemma always_now :
  forall (x: T) (s: infseq T) P, always P (Cons x s) -> P (Cons x s).
Proof.
intros x s P al. case (always_Cons x s P al); trivial.
Qed.

Lemma always_invar :
  forall (x: T) (s: infseq T) P, always P (Cons x s) -> always P s.
Proof.
intros x s P al. case (always_Cons x s P al); trivial.
Qed.

Lemma always_tl :
  forall (s: infseq T) P, always P s -> always P (tl s).
Proof.
intros (x, s). simpl. apply always_invar. 
Qed.

Lemma until_Cons :
  forall (x: T) (s: infseq T) J P,
  until J P (Cons x s) -> P (Cons x s) \/ (J (Cons x s) /\ until J P s).
Proof.
intros x s J P un. 
change (P (Cons x s) \/ (J (Cons x s) /\ until J P (tl (Cons x s)))).
destruct un; intuition.
Qed.

Lemma eventually_Cons :
  forall (x: T) (s: infseq T) P,
  eventually P (Cons x s) -> P (Cons x s) \/ eventually P s.
Proof.
intros x s P al. change (P (Cons x s) \/ eventually P (tl (Cons x s))). case al; auto.
Qed.

Lemma eventually_next : 
  forall (s: infseq T) P, eventually (next P) s -> eventually P s. 
Proof.
intros e P ev. induction ev as [(x, s) Ps | x s ev induc_hyp]. 
  constructor 2; constructor 1; exact Ps. 
  constructor 2. apply induc_hyp.
Qed.

Lemma eventually_always_cumul :
  forall (s: infseq T) P Q,
  eventually P s -> always Q s -> eventually (P /\_ always Q) s.
Proof.
induction 1 as [s Ps | x s evPs induc_hyp]. 
  intro al. constructor 1. split; assumption.
  intro al. constructor 2. apply induc_hyp. apply (always_invar _ _ _ al). 
Qed.

Lemma eventually_until_cumul :
  forall (s: infseq T) P J,
  eventually P s -> until J P s -> eventually (P /\_ until J P) s.
intros s P J ev. induction ev as [s Ps | x s evPs induc_hyp].
  intro un. constructor 1. split; assumption.
  intro unxs. case (until_Cons _ _ _ _ unxs). 
    intro Pxs. constructor 1; split; assumption. 
    intros (_, uns). constructor 2. apply induc_hyp. exact uns. 
Qed.

(* *)

Lemma always_always1 :
   forall P (s: infseq T), (always (now P) s) <-> (always1 P s).
Proof.
intros P s. split; genclear s. 
  cofix alwn.
  intros s a; case a; clear a s. intros (x, s); simpl. constructor.
    assumption. 
    apply alwn; assumption. 
  
  cofix alwn. destruct 1. constructor; simpl.
    assumption. 
    apply alwn; assumption. 
Qed.

(* *)

Lemma always_always_eventually :
   forall (P: infseq T -> Prop) (s : infseq T), always P s -> always (eventually P) s.
Proof.
intros P. cofix f. intros s a. destruct a. constructor. 
   constructor 1. assumption.
   apply f. assumption.
Qed.

(* *)

Lemma now_monotonic :
  forall (P Q: T -> Prop), 
  (forall x, P x -> Q x)    ->   forall s, now P s -> now Q s.
Proof.
intros P Q PQ (x, s) nP; simpl. apply PQ. assumption.
Qed.

Lemma consecutive_monotonic :
  forall (P Q: T -> T -> Prop), 
  (forall x y, P x y -> Q x y)    ->   forall s, consecutive P s -> consecutive Q s.
Proof.
intros P Q PQ (x, (y, s)) nP; simpl. apply PQ. assumption.
Qed.

Lemma always_monotonic :
  forall (P Q: infseq T -> Prop),
  (forall s, P s -> Q s)   ->   forall s, always P s -> always Q s.
Proof.
intros P Q PQ.  cofix cf. intros(x, s) a. 
generalize (always_Cons x s P a); simpl; intros (a1, a2). constructor; simpl.
  apply PQ. assumption. 
  apply cf. assumption. 
Qed.

Lemma until_monotonic :
  forall (P Q J K: infseq T -> Prop),
  (forall s, P s -> Q s) -> (forall s, J s -> K s) -> 
  forall s, until J P s -> until K Q s.
Proof.
intros P Q J K PQ JK.  cofix cf. intros(x, s) un. 
generalize (until_Cons x s J P un); simpl. intros [Pxs | (Jxs, uns)]. 
  constructor 1; simpl; auto. 
  constructor 2; simpl; auto. 
Qed.

Lemma eventually_trans :
  forall (P Q inv: infseq T -> Prop), 
  (forall x s, inv (Cons x s) -> inv s) ->
  (forall s, inv s -> P s -> eventually Q s) -> 
  forall s, inv s -> eventually P s -> eventually Q s.
Proof.
intros P Q inv is_inv PeQ s invs ev. induction ev as [s Ps | x s ev IHev]. 
  apply PeQ; assumption.  
  constructor 2. apply IHev. apply is_inv with x; assumption.
Qed.

Lemma eventually_monotonic :
  forall (P Q J: infseq T -> Prop), 
  (forall x s, J (Cons x s) -> J s) ->
  (forall s, J s -> P s -> Q s) -> 
  forall s, J s -> eventually P s -> eventually Q s.
Proof.
intros P Q J is_inv JPQ s Js ev. 
apply (eventually_trans P Q J is_inv); try assumption. 
  intros; constructor 1. apply JPQ; assumption. 
Qed.

(* corollary which turns out to be too weak in practice *)
Lemma eventually_monotonic_simple :
  forall (P Q: infseq T -> Prop), 
  (forall s, P s -> Q s) -> 
  forall s, eventually P s -> eventually Q s.
Proof.
intros P Q PQ s. 
apply (eventually_monotonic P Q (fun s:infseq T => True)); auto.
Qed.


Lemma until_eventually :
  forall (P Q J: infseq T -> Prop), 
  (forall s, J s -> P s -> Q s) -> 
  forall s, J s -> until J Q s -> eventually P s -> eventually Q s.
Proof.
intros P Q J impl s Js J_until_Q ev.
genclear J_until_Q; genclear Js.
induction ev as [s Ps | x s ev induc_hyp]. 
  intros Js J_until_Q. constructor 1. apply impl; assumption. 
  intros _ J_until_Q. cut (s = tl (Cons x s)); [idtac | reflexivity].
  case J_until_Q; clear J_until_Q x. 
    constructor 1; assumption.

    intros (x, s1) _ J_until_Q e; simpl in *.
    constructor 2. generalize e J_until_Q; clear e x. (* trick: keep J_until_Q!! *)
    case J_until_Q; clear J_until_Q s1.
       clearall. constructor 1; assumption. 
       intros s2 Js2 _ e J_until_Q2. rewrite e in induc_hyp; clear e. 
       apply induc_hyp; assumption. 
Qed.

End sec_modal_op_lemmas.

Implicit Arguments always_Cons [T x s P]. 
Implicit Arguments always_now [T x s P]. 
Implicit Arguments always_invar [T x s P]. 
Implicit Arguments always_tl [T s P]. 
Implicit Arguments eventually_next [T P s]. 
Implicit Arguments until_Cons [T x s J P]. 
Implicit Arguments eventually_Cons [T x s P]. 
Implicit Arguments eventually_always_cumul [T s P Q].
Implicit Arguments eventually_until_cumul [T s P J].
Implicit Arguments until_eventually [T P Q s J].

Implicit Arguments now_monotonic [T P Q s]. 
Implicit Arguments consecutive_monotonic [T P Q s]. 
Implicit Arguments eventually_monotonic [T P Q s]. 
Implicit Arguments eventually_monotonic_simple [T P Q s]. 
Implicit Arguments always_monotonic [T P Q s]. 
Implicit Arguments until_monotonic [T P Q J K s]. 


Ltac monotony := 
  match goal with 
     | [ |- now ?P ?s -> now ?Q ?s ] => apply now_monotonic
     | [ |- consecutive ?P ?s -> consecutive ?Q ?s ] =>
       apply consecutive_monotonic
     | [ |- always ?P ?s -> always ?Q ?s ] => apply always_monotonic
     | [ |- ?J ?s -> eventually ?P ?s -> eventually ?Q ?s ] =>
       apply eventually_monotonic
     | [ |- until ?J ?P ?s -> until ?K ?Q ?s ] => apply until_monotonic
  end.


(* --------------------------------------------------------------------------- *)
(* Extensional equality and temporal logic *)

Section sec_exteq_congruence.

Variable T: Type. 

(* All useful predicates are extensional in the following sense *)
Definition extensional (P: infseq T -> Prop) :=
  forall s1 s2, exteq_infseq s1 s2 -> P s1 -> P s2.

Lemma extensional_and:
  forall (P Q: infseq T -> Prop), 
  extensional P -> extensional Q -> extensional (P /\_ Q).
Proof. 
intros P Q eP eQ s1 s2 e. destruct e; simpl. unfold and_tl. intuition.
  apply eP with (Cons x s1); [constructor; assumption | assumption]. 
  apply eQ with (Cons x s1); [constructor; assumption | assumption]. 
Qed.

Lemma extensional_or:
  forall (P Q: infseq T -> Prop),
  extensional P -> extensional Q -> extensional (P \/_ Q).
Proof. 
intros P Q eP eQ s1 s2 e. destruct e; simpl. unfold or_tl. intuition.
  left; apply eP with (Cons x s1); [constructor; assumption | assumption]. 
  right; apply eQ with (Cons x s1); [constructor; assumption | assumption]. 
Qed.

Lemma extensional_impl:
  forall (P Q: infseq T -> Prop),
  extensional P -> extensional Q -> extensional (P ->_ Q).
Proof. 
intros P Q eP eQ s1 s2 e. destruct e; simpl. unfold impl_tl. 
intros PQ1 P2. 
  apply eQ with (Cons x s1); [constructor; assumption | idtac]. 
  apply PQ1. apply eP with (Cons x s2). 
    constructor. apply exteq_sym. assumption. 
    assumption. 
Qed.

(* *)

Lemma extensional_now:
  forall (P: T -> Prop), extensional (now P).
Proof. 
intros P s1 s2 e. destruct e; simpl. trivial.
Qed.

Lemma extensional_consecutive:
  forall (P: T -> T -> Prop), extensional (consecutive P).
Proof. 
intros P s1 s2 e. do 2 destruct e; simpl. trivial.
Qed.

Lemma extensional_eventually:
  forall (P: infseq T -> Prop), 
  extensional P -> extensional (eventually P). 
Proof.
intros P eP s1 s2 e ev1. genclear e; genclear s2. 
induction ev1 as [s1 ev1 | x1 s1 ev1 induc_hyp].
  intros s2 e. constructor 1. apply eP with s1; assumption. 
  intros (x2, s2) e. constructor 2. apply induc_hyp. 
    case (exteq_infseq_inversion e). trivial.  
Qed.

Lemma extensional_always:
  forall (P: infseq T -> Prop),
  extensional P -> extensional (always P). 
Proof.
intros P eP. cofix cf. 
intros (x1, s1) (x2, s2) e al1. case (always_Cons al1); intros Px1s1 als1. constructor. 
  eapply eP; eassumption. 
  simpl. apply cf with s1; try assumption. case (exteq_infseq_inversion e); trivial.
Qed.


Lemma extensional_until:
  forall (P Q: infseq T -> Prop),
  extensional P -> extensional Q -> extensional (until P Q). 
Proof.
intros P Q eP eQ. cofix cf. 
intros (x1, s1) (x2, s2) e un1. case (until_Cons un1). 
  intro Q1. constructor 1. eapply eQ; eassumption.
  intros (Px1s1, uns1). constructor 2.
    eapply eP; eassumption. 
    simpl. apply cf with s1; try assumption. case (exteq_infseq_inversion e); trivial.
Qed.


End sec_exteq_congruence.

Implicit Arguments extensional [T].

(* --------------------------------------------------------------------------- *)
(* Map and  temporal logic *)

Section sec_map_modalop.

Variable A B: Type.

Lemma and_Map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (Map f s)) ->
   (forall s, P' s -> Q' (Map f s)) ->
   forall (s: infseq A),
   (P /\_ P') s -> (Q /\_ Q') (Map f s).
Proof.
unfold and_tl; intuition. 
Qed.

Lemma and_Map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (Map f s) -> P s) ->
   (forall s, Q' (Map f s) -> P' s) ->
   forall (s: infseq A),
   (Q /\_ Q') (Map f s) -> (P /\_ P') s.
Proof.
unfold and_tl; intuition. 
Qed.

Lemma or_Map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (Map f s)) ->
   (forall s, P' s -> Q' (Map f s)) ->
   forall (s: infseq A),
   (P \/_ P') s -> (Q \/_ Q') (Map f s).
Proof.
unfold or_tl; intuition. 
Qed.

Lemma or_Map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (Map f s) -> P s) ->
   (forall s, Q' (Map f s) -> P' s) ->
   forall (s: infseq A),
   (Q \/_ Q') (Map f s) -> (P \/_ P') s.
Proof.
unfold or_tl; intuition. 
Qed.

Lemma impl_Map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (Map f s) -> P s) ->
   (forall s, P' s -> Q' (Map f s)) ->
   forall (s: infseq A),
   (P ->_ P') s -> (Q ->_ Q') (Map f s).
Proof.
unfold impl_tl; intuition. 
Qed.

Lemma impl_Map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (Map f s)) ->
   (forall s, Q' (Map f s) -> P' s) ->
   forall (s: infseq A),
   (Q ->_ Q') (Map f s) -> (P ->_ P') s.
Proof.
unfold impl_tl; intuition. 
Qed.

(* *)

Lemma now_Map :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   now (fun x => P (f x)) s -> now P (Map f s).
Proof.
intros f P (x, s) nP; assumption. 
Qed.

Lemma now_Map_conv :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   now P (Map f s) -> now (fun x => P (f x)) s.
Proof.
intros f P (x, s) nP; assumption. 
Qed.

Lemma consecutive_Map :
   forall (f: A->B) (P: B->B->Prop) (s: infseq A),
   consecutive (fun x y => P (f x) (f y)) s -> consecutive P (Map f s).
Proof.
intros f P (x, (y, s)) nP; assumption. 
Qed.

Lemma consecutive_Map_conv :
   forall (f: A->B) (P: B->B->Prop) (s: infseq A),
   consecutive P (Map f s) -> consecutive (fun x y => P (f x) (f y)) s.
Proof.
intros f P (x, (y, s)) nP; assumption. 
Qed.

Lemma always_Map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (Map f s)) ->
   forall (s: infseq A), always P s -> always Q (Map f s).
Proof.
intros f P Q PQ. cofix cf.
intros (x, s) a. case (always_Cons a); intros a1 a2. constructor.
  apply PQ. assumption.
  rewrite Map_Cons; simpl. apply cf; assumption.
Qed.

Lemma always_Map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (Map f s) -> P s) ->
   forall (s: infseq A), always Q (Map f s) -> always P s.
Proof.
intros f P Q QP. cofix cf.
intros (x, s) a. rewrite Map_Cons in a. case (always_Cons a); intros a1 a2. constructor.
  apply QP. rewrite Map_Cons; assumption.
  simpl. apply cf; assumption. 
Qed.

Lemma until_Map :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, J s -> K (Map f s)) ->
   (forall s, P s -> Q (Map f s)) ->
   forall (s: infseq A),
   (until J P) s -> (until K Q) (Map f s).
Proof.
intros f J P K Q JK PQ. cofix cf. 
intros (x, s) un. case (until_Cons un); clear un.
  intro Pxs; constructor 1. apply PQ. assumption. 
  intros (Jxs, un). rewrite Map_Cons. constructor 2.
    rewrite <- Map_Cons. auto.
    simpl. auto. 
Qed.

Lemma until_Map_conv :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, K (Map f s) -> J s) ->
   (forall s, Q (Map f s) -> P s) ->
   forall (s: infseq A),
   (until K Q) (Map f s) -> (until J P) s.
Proof.
intros f J P K Q KJ QP. cofix cf.
intros (x, s) un.
rewrite Map_Cons in un; case (until_Cons un); clear un; rewrite <- Map_Cons.
  intro Qxs; constructor 1. apply QP. assumption.
  intros (Kxs, un). constructor 2; simpl; auto.
Qed.

Lemma eventually_Map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (Map f s)) ->
   forall s, eventually P s -> eventually Q (Map f s).
Proof.
intros f P Q PQ s e. induction e as [s ok | x s e induc_hyp].
  destruct s as (x, s); simpl in *. rewrite Map_Cons. constructor 1.
    rewrite <- Map_Cons. apply PQ. exact ok.
  rewrite Map_Cons. constructor 2. exact induc_hyp.
Qed.

(* The converse seems to require much more work *)

Definition fstAB := fst (A:=A) (B:=B).

Lemma exteq_fst_zip:
  forall sA sB, exteq_infseq (Map fstAB (zip sA sB)) sA.
Proof.
cofix cf. intros (a, sA) (b, sB). 
rewrite zip_Cons. rewrite Map_Cons. constructor. apply cf.
Qed.

Lemma exteq_zip_Map :
   forall (f: A->B) (sA: infseq A) (sB: infseq B),
   always (now (fun c: A*B => let (x, y) := c in y = f x)) (zip sA sB) ->
   exteq_infseq sB (Map f (Map fstAB (zip sA (Map f sA)))).
Proof. 
intros f. cofix cf. 
intros (a, sA) (b, sB).
repeat rewrite Map_Cons; repeat rewrite zip_Cons; repeat rewrite Map_Cons; simpl. 
intro al; case (always_Cons al); clear al; simpl. intros e al. case e. constructor. 
apply cf. exact al. 
Qed.


Lemma eventually_Map_conv_aux :
   forall (f: A->B) (Q: infseq B->Prop), extensional Q ->
   forall (s: infseq A) (sB: infseq B),
   always (now (fun c: A*B => let (x, y) := c in y = f x)) (zip s sB) ->
   eventually Q sB ->
   eventually (fun sc => Q (Map f (Map fstAB sc))) (zip s (Map f s)).
Proof.
intros f Q extQ s sB al ev. genclear al; genclear s. 
induction ev as [(b, sB) QbsB | b sB ev induc_hyp].
  intros (a, sA) al.
  constructor 1. apply extQ with (Cons b sB); try assumption.
     apply exteq_zip_Map. apply al.

  intros (a, sA). repeat rewrite Map_Cons. repeat rewrite zip_Cons.
  intro al. case (always_Cons al); simpl. clear al; intros e al. 
  constructor 2. apply induc_hyp. exact al. 
Qed.


Lemma eventually_Map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q -> 
   (forall s, Q (Map f s) -> P s) ->
   forall s, eventually Q (Map f s) -> eventually P s.
Proof.
intros f P Q extP extQ QP s ev.
assert (efst: eventually P (Map fstAB (zip s (Map f s)))).
   assert (evzip : eventually (fun sc => Q (Map f (Map fstAB sc))) (zip s (Map f s))).
     clear extP QP P. 
     assert (alzip : (always (now (fun c : A * B => let (x, y) := c in y = f x)) (zip s (Map f s)))).
        clear ev extQ. generalize s; clear s. cofix cf. intros (x, s). constructor. 
          simpl. reflexivity. 
          simpl. apply cf. 

     apply (eventually_Map_conv_aux f Q extQ s (Map f s) alzip ev). 
   clear ev. induction evzip as [((a, b), sAB) QabsAB | c sAB _ induc_hyp].
      constructor 1; simpl. apply QP. assumption. 
      rewrite Map_Cons. constructor 2. apply induc_hyp. 
genclear efst. apply extensional_eventually.
  exact extP. 
  apply exteq_fst_zip.
Qed.


(* Some corollaries *)

Lemma eventually_now_Map :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   eventually (now (fun x => P (f x))) s -> eventually (now P) (Map f s).
Proof.
intros f P. apply eventually_Map. apply now_Map.
Qed.


Lemma eventually_now_Map_conv :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   eventually (now P) (Map f s) -> eventually (now (fun x => P (f x))) s.
Proof.
intros f P s. apply eventually_Map_conv.
  apply extensional_now. 
  apply extensional_now. 
  clear s. intros (x, s). repeat rewrite Map_Cons. simpl. trivial.
Qed.

Lemma ev_Map_now_eq :
  forall (f: A -> B) a s, eventually (now (eq a)) s -> 
  eventually (now (eq (f a))) (Map f s).
Proof.
intros f a. apply eventually_Map.
intros s noa. apply now_Map.
genclear noa. monotony. apply f_equal.
Qed.

End sec_map_modalop. 

(* TODO: implicit arguments for others *)
Implicit Arguments eventually_Map_conv [A B f P s].
Implicit Arguments eventually_now_Map_conv [A B f P s].



(* --------------------------------------------------------------------------- *)
(* Infinite subsequences *)

Section sec_subseq.
Variable T: Type.

(* suff s s'  means  s is a suffix of s' *)
Inductive suff (s : infseq T) : infseq T -> Prop :=
  | sp_eq : suff s s
  | sp_next : forall x s0, suff s s0 -> suff s (Cons x s0).

(* simple but not the most useful -- useless indeed *)
CoInductive subseq : infseq T -> infseq T -> Prop :=
  | Subseq : forall s s0 s1,
             suff s1 s0 -> subseq s (tl s1) -> subseq (Cons (hd s1) s) s0.

CoInductive subseqs' : infseq (infseq T) -> infseq T -> Prop :=
  | Subseqs' : forall si s0 s1,
             suff s1 s0 -> subseqs' si (tl s1) -> subseqs' (Cons s1 si) s0. 

CoInductive subseqs : infseq (infseq T) -> infseq T -> Prop :=
  | Subseqs : forall si s,
             suff (hd si) s -> subseqs (tl si) (tl (hd si)) -> subseqs si s. 

Lemma subseqs_subseqs' : forall si s, subseqs si s -> subseqs' si s.
Proof.
cofix subsub. 
intros si s su. case su; clear su si s. 
intros (s1, si) s0. simpl. intros su sb. constructor. 
  assumption. 
  apply subsub. assumption. 
Qed.

Lemma subseqs'_subseqs : forall si s, subseqs' si s -> subseqs si s.
cofix subsub. 
intros si s su. case su; clear su si s. 
intros si s0 s1 su sb. constructor; simpl. 
  assumption. 
  apply subsub. assumption. 
Qed.

(* Relating inf subseq to infinitely often *)

(* In the next lemma, always1 is bit overkill, but is just what is needed below *)
Lemma subseqs_eventually : 
  forall P si s, subseqs si s -> always1 P si -> eventually P s.
Proof.
intros P si s su. destruct su as [si s sf _].
induction sf as [ | x s0 _ Hrec]; intro a. 
  constructor 1. case a; simpl. intros; assumption.
  constructor 2. apply Hrec. apply a.
Qed.

Lemma subseqs_tl : forall si s, subseqs si (tl s) -> subseqs si s. 
Proof.
intros si (x, s) su. simpl in su. 
case su. clear su si s; intros si s sf su. 
constructor. 
  constructor 2. exact sf. 
  exact su. 
Qed.

Theorem subseq_inf_often :
  forall P si s, subseqs si s -> always1 P si -> inf_often P s.
Proof.
intros P. red. cofix sio.
intros si s su a.
constructor.
  apply subseqs_eventually with si; assumption.

  genclear a. case su. 
  clear su si s; intros (s0, si) s sf su a; simpl in * |- * . 
  apply (sio si); clear sio.
    induction sf; simpl.
      trivial. 
      apply subseqs_tl. assumption (* induction hyp *). 

    change (always1 P (tl (Cons s0 si))). case a; simpl; trivial. 
Qed.


(* Conversely : TODO *)

Inductive ex_suff (P: infseq T -> Prop) (s' : infseq T) : Prop :=
  Esp : forall s, suff s s' -> P s -> ex_suff P s'.

Theorem eventually_suff :
   forall P s', eventually P s' -> ex_suff P s'.
Proof.
intros P s ev. induction ev. 
  
  exists s; [ constructor | assumption]. 

  destruct IHev. exists s0. 
    constructor; assumption. 
    assumption. 
Qed.



(* Extensional version *)

CoInductive bisim : infseq T -> infseq T -> Prop :=
  | bisim_next : forall x s s', bisim s s' -> bisim (Cons x s) (Cons x s').

Inductive suff_bisim (s : infseq T) : infseq T -> Prop :=
  | sb_eq : forall s', bisim s s' -> suff_bisim s s'
  | sb_next : forall x s', suff_bisim s s' -> suff_bisim s (Cons x s').

Inductive suffb (x : T) (s : infseq T) : infseq T -> Prop :=
  | sp_eqb : forall s', bisim (Cons x s) s' -> suffb x s s'
  | sp_nextb : forall y s', suffb x s s' -> suffb x s (Cons y s').

CoInductive subseqb : infseq T -> infseq T -> Prop :=
  | Subseqb : forall x s s', suffb x s s' -> subseqb s s' -> subseqb (Cons x s) s'.

Inductive mem (x : T) : infseq T -> Prop :=
  | mem0 : forall s, mem x (Cons x s)
  | mem_next : forall y s, mem x s -> mem x (Cons y s).

Lemma subseqb_included : forall x s, mem x s -> forall s', subseqb s s' -> mem x s'.
induction 1 as [| y s M IHmem].
  inversion_clear 1 as [a b c ssp _]. induction ssp as [s' ssp | ].
    inversion_clear ssp. constructor. 
    constructor. assumption. 
  inversion_clear 1. apply IHmem; assumption. 
Qed.



End sec_subseq. 
