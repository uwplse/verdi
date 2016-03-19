Require Import Verdi.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section SeqNum.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.

  Record seq_num_data := mkseq_num_data { tdNum  : nat;
                            tdSeen : name -> list nat;
                            tdData : data }.

  Record seq_num_msg := mkseq_num_msg { tmNum : nat;
                          tmMsg : msg }.

  Definition seq_num_msg_eq_dec (x y : seq_num_msg) : {x = y} + {x <> y}.
    decide equality.
    apply msg_eq_dec.
    decide equality.
  Defined.

  Fixpoint processPackets (seq_num : nat) (packets : list (name * msg)) : nat * list (name * seq_num_msg) :=
    match packets with
      | [] => (seq_num, [])
      | p :: ps => let (n', pkts) := processPackets seq_num ps in
                   (n' + 1, (fst p, mkseq_num_msg n' (snd p)) :: pkts)
    end.


  Definition seq_num_init_handlers (n : name) :=
    mkseq_num_data 0 (fun _ => []) (init_handlers n).

  Definition seq_num_net_handlers
             (dst : name)
             (src : name)
             (m : seq_num_msg)
             (state : seq_num_data) :
    (list output) * seq_num_data * list (name * seq_num_msg) :=
    if (member (tmNum m) (tdSeen state src)) then
      ([], state, [])
    else
      let '(out, data', pkts) := (net_handlers dst src (tmMsg m) (tdData state)) in
      let (n', tpkts) := processPackets (tdNum state) pkts in
      (out, mkseq_num_data n' (update (tdSeen state) src (tmNum m :: tdSeen state src)) data', tpkts).

  Definition seq_num_input_handlers
             (h : name)
             (inp : input)
             (state : seq_num_data) :
    (list output) * seq_num_data * list (name * seq_num_msg) :=
    let '(out, data', pkts) := (input_handlers h inp (tdData state)) in
    let (n', tpkts) := processPackets (tdNum state) pkts in
    (out, mkseq_num_data n' (tdSeen state) data', tpkts).

  Instance base_params : BaseParams :=
    {
      data := seq_num_data ;
      input := input ;
      output := output
    }.

  Instance multi_params : MultiParams _ :=
    {
      name := name ;
      msg := seq_num_msg ;
      msg_eq_dec := seq_num_msg_eq_dec ;
      name_eq_dec := name_eq_dec ;
      nodes := nodes ;
      init_handlers := seq_num_init_handlers;
      net_handlers := seq_num_net_handlers;
      input_handlers := seq_num_input_handlers
    }.
  Proof.
    - eauto using all_names_nodes.
    - eauto using no_dup_nodes.
  Defined.
End SeqNum.

Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@MultiParams _) => apply multi_params : typeclass_instances.
