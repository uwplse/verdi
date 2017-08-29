Require Import Verdi.Verdi.

Require Import Cheerios.Cheerios.

Set Implicit Arguments.

Section Disk.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {data_serializer : Serializer data}.

  Definition init_disk (h : name) : IOStreamWriter.wire :=
    serialize_top (serialize (init_handlers h)).
  
  Definition disk_net_handlers dst src m st :=
    let '(out, data, ps) := net_handlers dst src m st in
    (serialize_top (serialize data), out, data, ps).

  Definition disk_input_handlers h inp st :=
    let '(out, data, ps) := input_handlers h inp st in
    (serialize_top (serialize data), out, data, ps).

  Instance disk_base_params : BaseParams := orig_base_params.

  Instance disk_multi_params : DiskMultiParams disk_base_params :=
    {
      d_name := name;
      d_name_eq_dec := name_eq_dec;
      d_msg := msg;
      disk := IOStreamWriter.wire;
      d_msg_eq_dec := msg_eq_dec;
      d_nodes := nodes;
      d_all_names_nodes := all_names_nodes;
      d_no_dup_nodes := no_dup_nodes;
      d_init_handlers := init_handlers;
      d_init_disk := init_disk;
      d_net_handlers := disk_net_handlers;
      d_input_handlers := disk_input_handlers
    }.

  Instance disk_failure_params : DiskFailureParams disk_multi_params :=
    {
      d_reboot :=
        fun n s =>
          reboot
            (match deserialize_top deserialize s with
              | Some d => d
              | None => init_handlers n
             end)
    }.
End Disk.

Hint Extern 5 (@BaseParams) => apply disk_base_params : typeclass_instances.
Hint Extern 5 (@DiskMultiParams _) => apply disk_multi_params : typeclass_instances.
Hint Extern 5 (@DiskFailureParams _ _) => apply disk_failure_params : typeclass_instances.
