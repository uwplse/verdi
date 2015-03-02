Require Import List.
Import ListNotations.
Require Import Arith.

Require Import Net.
Require Import Util.

Require Import Raft.
Require Import CommonDefinitions.
Require Import OutputImpliesAppliedInterface.

Section CausalOrderPreserved.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Section inner.
  Variables client id client' id' : nat.

  Definition is_output (trace_entry : (name * (raft_input + list raft_output))) :=
    match trace_entry with
      | (_, inr os) => if in_output_list_dec client id os then true else false
      | _ => false
    end.

  Definition is_input (trace_entry : (name * (raft_input + list raft_output))) :=
    match trace_entry with
      | (_, inl (ClientRequest c i _)) => andb (beq_nat client' c) (beq_nat id' i)
      | _ => false
    end.

  Definition output_before_input (tr : list (name * (raft_input + list raft_output))) :=
    before_func is_output is_input tr.

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
