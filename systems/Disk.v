Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.

Require Import Cheerios.Cheerios.

Set Implicit Arguments.


Section Disk.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {data_serializer : Serializer data}.


  Definition init_disk h := serialize_top serialize (init_handlers h).
  
  Definition disk_net_handlers dst src m : GenHandler (name * msg) data output disk :=
    fun s =>
      match net_handlers dst src m s with
      | (out, data, packets) => 
      (serialize_top serialize data, out, data, packets)
    end.

  Definition disk_input_handlers h inp : GenHandler (name * msg) data output disk :=
    fun s =>
      match input_handlers h inp s with
      | (out, data, packets) => 
      (serialize_top serialize data, out, data, packets)
    end.

  Instance disk_params : DiskParams orig_base_params :=
    {
      d_name := name;
      d_name_eq_dec := name_eq_dec;
      d_msg := msg;
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
      d_reboot := deserialize_top (deserialize : ByteListReader.t data)
    }.

  Theorem disk_follows_local_state: forall net tr (node : d_name),
      step_async_disk_star (params := disk_params) step_async_disk_init net tr ->
      d_reboot (nwdDisk net node) = Some (nwdState net node).
  Proof.
    intros.
    remember step_async_disk_init as y in *.
    revert Heqy.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - simpl.
      unfold init_handlers.
      apply serialize_deserialize_top_id.
    - concludes.
      match goal with
      | [ H : step_async_disk _ _ _ |- _ ] => invc H
      end; simpl;
        break_if;
        try assumption;
        simpl in *; unfold disk_net_handlers, disk_input_handlers in *;
          repeat break_match;
          repeat find_inversion;
          apply serialize_deserialize_top_id.
  Qed.        
End Disk.