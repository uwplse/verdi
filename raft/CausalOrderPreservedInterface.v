Require Import List.
Import ListNotations.
Require Import Arith.

Require Import Net.
Require Import Util.

Require Import Raft.
Require Import CommonDefinitions.
Require Import TraceUtil.

Section CausalOrderPreserved.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Section inner.
  Variables client id client' id' : nat.

  Definition output_before_input (tr : list (name * (raft_input + list raft_output))) :=
    before_func (is_output_with_key client id) (is_input_with_key client' id') tr.

  Definition has_key (c : nat) (i : nat) (e : entry) :=
    match e with
      | mkEntry _ c' i' _ _ _ => andb (beq_nat c c') (beq_nat i i')
    end.

  Definition entries_ordered net :=
    before_func (has_key client id) (has_key client' id') (applied_entries (nwState net)).
  End inner.

  Class causal_order_preserved_interface : Prop :=
    {
      causal_order_preserved :
        forall client id client' id' failed net tr,
          step_f_star step_f_init (failed, net) tr ->
          output_before_input client id client' id' tr ->
          entries_ordered client id client' id' net
    }.
End CausalOrderPreserved.
