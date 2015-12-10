Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import VerdiTactics.


Require Import Net.
Require Import Util.
Require Import HandlerMonad.

Require Import Sorted.

Set Implicit Arguments.

Section OrderedSeqNum.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.


  Record seq_num_msg := mkseq_num_msg {
                            tmNum : nat;
                            tmMsg : msg }.


  Record seq_num_data := mkseq_num_data {
                             _tdNextToSend : name -> nat;
                             _tdNextToRecv : name -> nat;
                             _tdBuffer : name -> list seq_num_msg;
                             _tdData : data }.


  Definition seq_num_msg_eq_dec (x y : seq_num_msg) : {x = y} + {x <> y}.
    decide equality.
    apply msg_eq_dec.
    apply eq_nat_dec.
  Defined.

  Definition seq_num_init_handlers (n : name) :=
    mkseq_num_data (fun _ => 0) (fun _ => 0) (fun _ => []) (init_handlers n).

  Definition Handler (S : Type) := GenHandler (name * seq_num_msg) S output unit.

  Fixpoint insert (m : seq_num_msg) (ms : list seq_num_msg) : list seq_num_msg :=
    match ms with
    | [] => [m]
    | m' :: ms' => if m.(tmNum) <? m'.(tmNum) then m :: ms
                  else m' :: insert m ms'
    end.

  Record lens (Big Small : Type) : Type :=
    mkLens { _lensGet : Big -> Small;
             _lensPut : Small -> Big -> Big}.

  Definition lens_get {S A : Type} (l : lens S A) :
    GenHandler (name * seq_num_msg) S output A :=
    s <- get ;; ret (l.(_lensGet) s).

  Definition lens_put {S A : Type} (l : lens S A) (a : A) :
    GenHandler (name * seq_num_msg) S output unit :=
    s <- get ;; put (l.(_lensPut) a s).

  Definition lens_modify {S A : Type} (l : lens S A) (f : A -> A) :
    GenHandler (name * seq_num_msg) S output unit :=
    a <- lens_get l ;; lens_put l (f a).

  Definition buffer (n : name) : lens seq_num_data (list seq_num_msg) :=
    mkLens (fun s => _tdBuffer s n) (fun l s => mkseq_num_data
                                         (_tdNextToSend s)
                                         (_tdNextToRecv s)
                                         (update (_tdBuffer s) n l)
                                         (_tdData s)).

  Definition underlying_data : lens seq_num_data data :=
    mkLens _tdData (fun d s => mkseq_num_data
                              (_tdNextToSend s)
                              (_tdNextToRecv s)
                              (_tdBuffer s)
                              d).

  Definition nextToSend (n : name) : lens seq_num_data nat :=
    mkLens (fun s => _tdNextToSend s n) (fun x s =>
                                        mkseq_num_data
                                          (update (_tdNextToSend s) n x)
                                          (_tdNextToRecv s)
                                          (_tdBuffer s)
                                          (_tdData s)).

  Definition nextToRecv (n : name) : lens seq_num_data nat :=
    mkLens (fun s => _tdNextToRecv s n) (fun x s =>
                                        mkseq_num_data
                                          (_tdNextToSend s)
                                          (update (_tdNextToRecv s) n x)
                                          (_tdBuffer s)
                                          (_tdData s)).

  Fixpoint to_deliver (next : nat) (l : list seq_num_msg) :
    nat * list seq_num_msg * list seq_num_msg :=
    match l with
    | [] => (next, [], [])
    | x :: l' => if eq_nat_dec (tmNum x) next
                then let '(n, yes, no) := to_deliver (S next) l'
                     in (n, x :: yes, no)
                else (next, [], l)
    end.

  Fixpoint write_all_output (os : list output) : Handler seq_num_data :=
    match os with
    | [] => nop
    | o :: os' => write_output o ;; write_all_output os'
    end.

  Definition send_underlying_packet (h : name) (p : name * msg) : Handler seq_num_data :=
    let (dst, m) := p in
    n <- lens_get (nextToSend dst) ;;
    send (dst, mkseq_num_msg n m) ;;
    lens_put (nextToSend dst) (S n).

  Fixpoint send_underlying_packets h (packets : list (name * msg)) : Handler seq_num_data :=
    match packets with
    | [] => nop
    | p :: ps => send_underlying_packet h p ;; send_underlying_packets h ps
    end.


  Fixpoint deliver (dst src : name) (l : list seq_num_msg) : Handler seq_num_data :=
    match l with
    | [] => nop
    | x :: xs =>
      d <- lens_get underlying_data ;;
      let '(os, d', ps) := net_handlers dst src (tmMsg x) d in
      lens_put underlying_data d' ;;
      write_all_output os ;;
      send_underlying_packets dst ps
    end.

  Definition seq_num_net_handlers (dst src : name) (m : seq_num_msg) : Handler seq_num_data :=
    ms <- lens_get (buffer src) ;;
    let ms' := insert m ms in
    n <- lens_get (nextToRecv src) ;;
    let '(n', yes, no) := to_deliver n ms' in
    lens_put (nextToRecv src) n' ;;
    lens_put (buffer src) no ;;
    deliver dst src yes.

  Definition seq_num_input_handlers (h : name) (inp : input) : Handler seq_num_data :=
    d <- lens_get underlying_data ;;
    let '(os, d', ps) := input_handlers h inp d in
      lens_put underlying_data d' ;;
      write_all_output os ;;
      send_underlying_packets h ps.


  Instance ordered_seq_num_base_params : BaseParams :=
    {
      data := seq_num_data ;
      input := input ;
      output := output
    }.

  Instance ordered_seq_num_multi_params : MultiParams _ :=
    {
      name := name ;
      msg := seq_num_msg ;
      msg_eq_dec := seq_num_msg_eq_dec ;
      name_eq_dec := name_eq_dec ;
      nodes := nodes ;
      init_handlers := seq_num_init_handlers;
      net_handlers := fun dst src m d => runGenHandler_ignore d (seq_num_net_handlers dst src m);
      input_handlers := fun h i d => runGenHandler_ignore d (seq_num_input_handlers h i)
    }.
  Proof.
    - eauto using all_names_nodes.
    - eauto using no_dup_nodes.
  Defined.

  Notation underlying_network := (@ordered_network _ orig_multi_params).
  Notation transformed_network := (@network _ ordered_seq_num_multi_params).

  Notation underlying_packet := (@msg _ orig_multi_params).
  Notation transformed_packet := (@packet _ ordered_seq_num_multi_params).

  Fixpoint sort (l : list seq_num_msg) : list seq_num_msg :=
    match l with
    | [] => []
    | x :: xs => insert x (sort xs)
    end.

  Definition msg_le x y := tmNum x <= tmNum y.

  Lemma insert_preserves_HdRel :
    forall l a x,
      HdRel msg_le a l ->
      msg_le a x ->
      HdRel msg_le a (insert x l).
  Proof.
    destruct l; intros.
    - constructor; auto.
    - simpl. invc H.
      break_if; do_bool; auto.
  Qed.

  Lemma insert_preserves_sorted :
    forall x l,
      Sorted msg_le l ->
      Sorted msg_le (insert x l).
  Proof.
    induction l; intros.
    - repeat constructor.
    - simpl. break_if.
      + do_bool. constructor; [solve[auto]|]. constructor. red. auto with *.
      + invc H. constructor; [solve[auto]|]. do_bool. auto using insert_preserves_HdRel.
  Qed.

  Lemma sort_sorted :
    forall l,
      Sorted msg_le (sort l).
  Proof.
    induction l.
    - constructor.
    - simpl. auto using insert_preserves_sorted.
  Qed.

  Arguments sumbool_and {_} {_} {_} {_} _ _.

  Definition revertNetwork (net : transformed_network) : underlying_network.
  refine (@mkONetwork _ orig_multi_params
            (fun src dst => _)
            (fun nm => _tdData (nwState net nm))).
  refine (map tmMsg (sort _)).
  refine (filterMap (fun p : transformed_packet =>
                       if sumbool_and (name_eq_dec p.(pSrc) src)
                                      (name_eq_dec p.(pDst) dst)
                       then Some p.(pBody)
                       else None) (nwPackets net)).
  Defined.

  Lemma ordered_seq_num_step net net' tr :
    reachable step_m step_m_init net ->
    step_m net net' tr ->
    exists tr', step_o_star (revertNetwork net) (revertNetwork net') tr'.
  Proof.
    intros Hreach Hstep.
    invc Hstep.
    - simpl net_handlers in *.
      unfold runGenHandler_ignore in *.
      repeat break_let; find_inversion.
      {
        unfold seq_num_net_handlers in *.
        unfold lens_get, lens_put in *.
        monad_unfold.
        repeat break_let; repeat find_inversion.

      }



  Theorem ordered_seq_num_correct :
    forall (net : transformed_network) tr,
      step_m_star step_m_init net tr ->
      step_o_star step_o_init (revertNetwork net) tr.



End OrderedSeqNum.
(*
Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@MultiParams _) => apply multi_params : typeclass_instances.
*)