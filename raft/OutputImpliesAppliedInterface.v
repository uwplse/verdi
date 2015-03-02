Require Import List.
Require Import Arith.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
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

  Definition is_client_response (out : raft_output) : bool :=
    match out with
      | ClientResponse c i _ => andb (beq_nat client c) (beq_nat id i)
      | NotLeader _ _ => false
    end.

  Definition in_output_list_dec (os : list raft_output) :
    {in_output_list os} + {~ in_output_list os}.
  Proof.
    unfold in_output_list.
    destruct (find is_client_response os) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      unfold is_client_response in *. break_match; try discriminate.
      subst. do_bool. break_and. do_bool. subst. left. eauto.
    - right. intro. break_exists.
      eapply find_none in H; eauto. unfold is_client_response in *.
      find_apply_lem_hyp Bool.andb_false_elim. intuition; do_bool; congruence.
  Qed.

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
