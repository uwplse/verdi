Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.
Set Implicit Arguments.

Section Serialized.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {orig_name_overlay_params : NameOverlayParams orig_multi_params}.
  Context {orig_fail_msg_params : FailMsgParams orig_multi_params}.
  Context {orig_new_msg_params : NewMsgParams orig_multi_params}.
  Context {orig_msg_serializer : Serializer msg}.

  Definition serialize_name_msg_tuple (nm : name * msg) :=
    let (n, msg) := nm in
    (n, serialize_top (serialize msg)).

  Definition serialize_handler_result (res : (list output) * data * list (name * msg)) :=
    let '(outputs, data, messages) := res in
    (outputs, data, map serialize_name_msg_tuple messages).

  Definition serialized_net_handlers (dst : name) (src : name) (wm : IOStreamWriter.wire) (d : data) :=
    match deserialize_top deserialize wm with
    | None => ([], d, [])
    | Some m => serialize_handler_result (net_handlers dst src m d)
    end.

  Definition serialized_input_handlers (h : name) (inp : input) (d : data) :=
    serialize_handler_result (input_handlers h inp d).

  #[global] Instance serialized_base_params : BaseParams := orig_base_params.

  #[global] Instance serialized_multi_params : MultiParams _ :=
    {
      name := name;
      name_eq_dec := name_eq_dec;
      msg := IOStreamWriter.wire;
      msg_eq_dec := IOStreamWriter.wire_eq_dec;
      nodes := nodes;
      all_names_nodes := all_names_nodes;
      no_dup_nodes := no_dup_nodes;
      init_handlers := init_handlers;
      net_handlers := serialized_net_handlers;
      input_handlers := serialized_input_handlers;
    }.

  #[global] Instance serialized_failure_params : FailureParams serialized_multi_params :=
    {
      reboot := @reboot _ _ orig_failure_params
    }.

  #[global] Instance serialized_name_overlay_params : NameOverlayParams serialized_multi_params :=
    {
      adjacent_to := @adjacent_to _ _ orig_name_overlay_params;
      adjacent_to_dec := @adjacent_to_dec _ _ orig_name_overlay_params;
      adjacent_to_symmetric := @adjacent_to_symmetric _ _ orig_name_overlay_params;
      adjacent_to_irreflexive := @adjacent_to_irreflexive _ _ orig_name_overlay_params
    }.

  #[global] Instance serialized_fail_msg_params : FailMsgParams serialized_multi_params :=
    {
      msg_fail := serialize_top (serialize msg_fail)
    }.

  #[global] Instance serialized_new_msg_params : NewMsgParams serialized_multi_params :=
    {
      msg_new := serialize_top (serialize msg_new)
    }.
End Serialized.

#[global] Hint Extern 5 (@BaseParams) => apply serialized_base_params : typeclass_instances.
#[global] Hint Extern 5 (@MultiParams _) => apply serialized_multi_params : typeclass_instances.
#[global] Hint Extern 5 (@FailureParams _ _) => apply serialized_failure_params : typeclass_instances.
#[global] Hint Extern 5 (@NameOverlayParams _ _) => apply serialized_name_overlay_params : typeclass_instances.
#[global] Hint Extern 5 (@FailMsgParams _ _) => apply serialized_fail_msg_params : typeclass_instances.
#[global] Hint Extern 5 (@NewMsgParams _ _) => apply serialized_new_msg_params : typeclass_instances.
