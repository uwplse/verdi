Require Import Arith.
Require Import Nat.
Require Import Omega.
Require Import Util.
Require Import Net.
Require Import VerdiTactics.

Section SingleNodeUpdate.

  Record StateMachine :=
    {
      Input : Type;
      Output : Type;
      Data : Type;
      Handler : Input -> Data -> (Output * Data)
    }.

  Variable state_machines : list StateMachine.

  Variable update_data :
    forall i s1 s2,
      Nth state_machines i s1 ->
      Nth state_machines (S i) s1 ->
      Data s1 ->
      Data s2.

  Variable update_input :
    forall i s1 s2,
      Nth state_machines i s1 ->
      Nth state_machines (S i) s2 ->
      Input s1 ->
      Input s2.

  Definition Nth_S :
    forall A i (l : list A) x,
      Nth l (S i) x ->
      {y : A |
        Nth l i y}.
  Proof.
    induction i; intros; simpl in *.
    - destruct l; simpl in *.
      + inversion H.
      + (exists a). constructor.
    - destruct l; simpl in *.
      + inversion H.
      + inversion H. subst.
        apply IHi in H4.
        break_exists_exists.
        constructor. auto.
  Qed.

  Definition update_input_star :
    forall j i s1 s2,
      i <= j ->
      Nth state_machines i s1 ->
      Nth state_machines j s2 ->
      Input s1 ->
      Input s2.
  Proof.
    induction j; intros.
    - assert (i = 0) by omega.
      subst.
      repeat find_apply_lem_hyp Nth_nth_error.
      repeat find_rewrite. inversion H0. subst. auto.
    - find_apply_lem_hyp le_lt_eq_dec.
      intuition.
      + assert (i <= j) by omega.
        apply Nth_S in H1. 
        eapply update_input. 2:eauto.
        
      
      
      
    
      
  
  Variable N : nat.
  Definition index := {m | m <= N}.

  Definition next : index -> option index.
    intro i. destruct i.
    destruct (le_dec (S x) N).
    - exact (Some (exist _ (S x) l0)).
    - exact None.
  Defined.

  Definition zero : index.
    refine (exist _ 0 _). apply Peano.le_0_n.
  Defined.

  Definition index_le (x y : index) :=
    le (proj1_sig x) (proj1_sig y).

  Definition index_le_dec (x y : index) : {index_le x y} + {~ index_le x y} :=
    le_dec (proj1_sig x) (proj1_sig y).

  Variable Input : index -> Type.
  Variable Output : index -> Type.
  Variable Data : index -> Type.

  Variable update_data :
    forall i j,
      next i = Some j ->
      Data i ->
      Data j.

  Variable update_input :
    forall i j,
      next i = Some j ->
      Input i ->
      option (Input j).

  Definition update_input_star :
    forall i j,
      le i j ->
      Input i ->
      option (Input j).
    
      

  Variable update_output :
    forall i j,
      next i = Some j ->
      Output j ->
      option (Output i).

  Variable handlers :
    forall i,
      Input i -> Data i -> (Output i * Data i).

  Inductive step : {i : index & Data i} -> {j : index & Data j} ->
                   list {i : index & (Input i * option (Output i))%type} -> Prop :=
  | step_inp :
      forall 
                                                                                  
