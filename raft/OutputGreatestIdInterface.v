Require Import List.
Require Import Arith.

Require Import Net.
Require Import StructTact.Util.
Require Import StructTact.StructTactics.

Require Import Raft.
Require Import CommonDefinitions.
Require Import TraceStructTact.Util.

Section OutputGreatestId.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Section inner.

  Variables client id : nat.


  Definition greatest_id_for_client (net : network) : Prop :=
    forall id',
      id < id' ->
      before_func (has_key client id) (has_key client id') (applied_entries (nwState net)).
  
  End inner.

  Class output_greatest_id_interface : Prop :=
    {
      output_greatest_id :
        forall client id failed net tr,
          step_f_star step_f_init (failed, net) tr ->
          key_in_output_trace client id tr ->
          greatest_id_for_client client id net
    }.
End OutputGreatestId.
