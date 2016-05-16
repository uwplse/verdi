Require Import Verdi.
Require Import Cheerios.Types.

Set Implicit Arguments.

Section Serialized.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_data_serializer : Serializer data}.
  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  Definition serialize_name_msg_tuple (n_msg : (name * msg)) :=
    let (n, msg) := n_msg in
    (n, serialize msg).

  Definition serialize_handler_result (result : (list output) * data * list (name * msg)) :
    list (list bool) * list bool * list (name * list bool) :=
    let '(outputs, data, messages) := result in
    let outputsBits := map (@serialize output orig_output_serializer) outputs in
    let dataBits := serialize data in
    let messagesBits := map serialize_name_msg_tuple messages in
    (outputsBits, dataBits, messagesBits).

  Definition serialized_init_handlers (n : name) :=
    serialize (init_handlers n).

  Definition serialized_net_handlers
             (dst : name)
             (src : name)
             (mBits : list bool)
             (stateBits : list bool) :
    list (list bool) * list bool * list (name * list bool) :=
    match (deserialize mBits) with
    | None => ([], stateBits, [])
    | Some (m, rest) =>
      match (deserialize stateBits) with
      | None => ([], stateBits, [])
      | Some (state, rest) =>
        serialize_handler_result (net_handlers dst src m state)
      end
    end.

  Definition serialized_input_handlers
             (h : name)
             (inpBits : list bool)
             (stateBits : list bool) :
    list (list bool) * list bool * list (name * list bool) :=
    match (deserialize inpBits) with
    | None => ([], stateBits, [])
    | Some (inp, rest) =>
      match (deserialize stateBits) with
      | None => ([], stateBits, [])
      | Some (state, rest) =>
        serialize_handler_result (input_handlers h inp state)
      end
    end.

  Instance base_params : BaseParams :=
    {
      data := list bool;
      input := list bool;
      output := list bool
    }.

  Instance multi_params : MultiParams _ :=
    {
      name := @name _ orig_multi_params;
      name_eq_dec := name_eq_dec;
      msg := list bool;
      msg_eq_dec := (list_eq_dec Bool.bool_dec);
      nodes := nodes;
      init_handlers := serialized_init_handlers;
      net_handlers := serialized_net_handlers;
      input_handlers := serialized_input_handlers;
    }.
  Proof.
    - eauto using all_names_nodes.
    - eauto using no_dup_nodes.
  Qed.
End Serialized.

Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@MultiParams _) => apply multi_params : typeclass_instances.