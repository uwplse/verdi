Require Import Raft.
Require Import CommonDefinitions.
Require Import TraceUtil.

Section OutputImpliesApplied.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Section inner.

  Variables client id : nat.


  Definition in_applied_entries (net : network) : Prop :=
    exists e,
      eClient e = client /\
      eId e = id /\
      In e (applied_entries (nwState net)).

  End inner.

  Class output_implies_applied_interface : Prop :=
    {
      output_implies_applied :
        forall client id failed net tr,
          step_failure_star step_failure_init (failed, net) tr ->
          key_in_output_trace client id tr ->
          in_applied_entries client id net
    }.
End OutputImpliesApplied.
