Require Import Verdi.Verdi.

Require Import Cheerios.Cheerios.

Set Implicit Arguments.

Section Disk.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {data_serializer : Serializer data}.

  Definition disk := IOStreamWriter.wire.

  Definition init_disk h := serialize_top serialize (init_handlers h).
  
  Definition disk_net_handlers dst src m st :=
    match net_handlers dst src m st with
    | (out, data, packets) => 
      (serialize_top serialize data, out, data, packets)
    end.

  Definition disk_input_handlers h inp st :=
    match input_handlers h inp st with
    | (out, data, packets) => 
      (serialize_top serialize data, out, data, packets)
    end.

  Instance base_params : BaseParams :=
    {
      data := data ;
      input := input ;
      output := output
    }.

  Instance disk_params : DiskParams base_params :=
    {
      d_name := name;
      d_name_eq_dec := name_eq_dec;
      d_msg := msg;
      disk := disk;
      d_msg_eq_dec := msg_eq_dec;
      d_nodes := nodes;
      d_all_names_nodes := all_names_nodes;
      d_no_dup_nodes := no_dup_nodes;
      d_init_handlers := init_handlers;
      d_init_disk := init_disk;
      d_net_handlers := disk_net_handlers;
      d_input_handlers := disk_input_handlers
    }.

  Instance disk_failure_params : DiskFailureParams disk_params :=
    {
      d_reboot := deserialize_top deserialize
    }.
End Disk.

Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@DiskParams _) => apply disk_params : typeclass_instances.
Hint Extern 5 (@DiskFailureParams _) => apply disk_failure_params : typeclass_instances.
