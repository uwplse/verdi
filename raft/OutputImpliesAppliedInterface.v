Require Import List.

Require Import Net.
Require Import Raft.

Require Import CommonDefinitions.

Section OutputImpliesApplied.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Section inner.

  Variables client id : nat.

  Definition in_output_list (os : list raft_output) :=
    exists o,
      In (ClientResponse client id o) os.

  Definition in_output (tr : list (name * (raft_input + list raft_output))) : Prop :=
    exists os h,
      In (h, inr os) tr /\
      in_output_list os.

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
          step_f_star step_f_init (failed, net) tr ->
          in_output client id tr ->
          in_applied_entries client id net
    }.
End OutputImpliesApplied.