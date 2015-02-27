Require Import List.
Require Import Net.
Require Import Raft.
Require Import CommonDefinitions.

Section AppliedImpliesInputInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Section inner.
    Variables client id : nat.

    Definition in_input (tr : list (name * (raft_input + list raft_output))) : Prop :=
      exists h i,
        In (h, inl (ClientRequest client id i)) tr.
  End inner.

  Class applied_implies_input_interface : Prop :=
    {
      applied_implies_input :
        forall client id failed net tr e,
          step_f_star step_f_init (failed, net) tr ->
          eClient e = client ->
          eId e = id ->
          In e (applied_entries (nwState net)) ->
          in_input client id tr
    }.
End AppliedImpliesInputInterface.