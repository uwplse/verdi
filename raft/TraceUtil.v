Require Import List.
Import ListNotations.
Require Import Arith.

Require Import Net.
Require Import VerdiTactics.
Require Import Util.
Require Import Raft.

Section TraceUtil.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition key_in_output_list (client id : nat) (os : list raft_output) :=
    exists o,
      In (ClientResponse client id o) os.

  Definition is_client_response_with_key (client id : nat) (out : raft_output) : bool :=
    match out with
      | ClientResponse c i _ => andb (beq_nat client c) (beq_nat id i)
      | NotLeader _ _ => false
    end.

  Definition key_in_output_list_dec (client id : nat) (os : list raft_output) :
    {key_in_output_list client id os} + {~ key_in_output_list client id os}.
  Proof.
    unfold key_in_output_list.
    destruct (find (is_client_response_with_key client id) os) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      unfold is_client_response_with_key in *. break_match; try discriminate.
      subst. do_bool. break_and. do_bool. subst. left. eauto.
    - right. intro. break_exists.
      eapply find_none in H; eauto. unfold is_client_response_with_key in *.
      find_apply_lem_hyp Bool.andb_false_elim. intuition; do_bool; congruence.
  Qed.

  Definition key_in_output_trace (client id : nat)
             (tr : list (name * (raft_input + list raft_output))) : Prop :=
    exists os h,
      In (h, inr os) tr /\
      key_in_output_list client id os.

  Definition key_in_input_trace (client id : nat)
             (tr : list (name * (raft_input + list raft_output))) : Prop :=
      exists h i,
        In (h, inl (ClientRequest client id i)) tr.
  
  Definition is_output_with_key (client id : nat)
             (trace_entry : (name * (raft_input + list raft_output))) :=
    match trace_entry with
      | (_, inr os) => if key_in_output_list_dec client id os then true else false
      | _ => false
    end.

  Definition is_input_with_key (client id: nat)
             (trace_entry : (name * (raft_input + list raft_output))) :=
    match trace_entry with
      | (_, inl (ClientRequest c i _)) => andb (beq_nat client c) (beq_nat id i)
      | _ => false
    end.
End TraceUtil.
