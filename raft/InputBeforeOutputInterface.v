Require Import Raft.
Require Import CommonDefinitions.
Require Import TraceUtil.

Section InputBeforeOutputInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Section inner.
  Variables client id : nat.

  Definition input_before_output (tr : list (name * (raft_input + list raft_output))) :=
    before_func (is_input_with_key client id) (is_output_with_key client id) tr.
  End inner.

  Class input_before_output_interface : Prop :=
    {
      output_implies_input_before_output :
        forall client id failed net tr,
          step_f_star step_f_init (failed, net) tr ->
          key_in_output_trace client id tr ->
          input_before_output client id tr
    }.
End InputBeforeOutputInterface.
