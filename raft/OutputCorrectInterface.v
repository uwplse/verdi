Require Import Raft.
Require Import CommonDefinitions.
Require Import TraceUtil.

Section OutputCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Class output_correct_interface : Prop :=
    {
      output_correct_invariant :
        forall client id out failed net tr,
          step_failure_star step_failure_init (failed, net) tr ->
          in_output_trace client id out tr ->
          output_correct client id out (applied_entries (nwState net))
    }.
End OutputCorrect.
