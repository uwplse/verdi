Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Bool.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.

Section RaftLinearizableDefinitions.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Fixpoint check_concurrency_outputs
           (os : list raft_output)
           (env : nat -> option nat) {struct os} : (nat -> option nat) :=
    match os with
      | [] => env
      | ClientResponse c id o :: os' =>
        match env c with
          | None => check_concurrency_outputs os' env
          | Some id' => if beq_nat id id'
                        then check_concurrency_outputs os'
                               (fun client => if beq_nat c client then None
                                              else env client)
                        else check_concurrency_outputs os' env
        end
      | NotLeader _ _ :: os' => check_concurrency_outputs os' env
    end.

  Fixpoint check_concurrency'
           (tr : list (name * (raft_input + list raft_output)))
           (env : nat -> option nat) {struct tr} : bool :=
    match tr with
      | [] => true
      | (_ , ev) :: tr' =>
        match ev with
          | inl (ClientRequest c id i) =>
            match env c with
              | None => check_concurrency' tr' (fun client => if beq_nat c client then Some id
                                                             else env client)
              | Some id' => (id <=? id') && check_concurrency' tr' env
            end
          | inl Timeout => check_concurrency' tr' env
          | inr os => check_concurrency' tr' (check_concurrency_outputs os env)
        end
    end.

  Lemma check_concurrency'_snoc_inv :
    forall tr ev env,
      check_concurrency' (tr ++ [ev]) env = true ->
      check_concurrency' tr env = true.
  Proof.
    induction tr; intros.
    - auto.
    - simpl in *. repeat break_match; subst; do_bool; intuition eauto.
  Qed.

  Definition check_concurrency tr := check_concurrency' tr (fun _ => None).

  Example CC_nil : check_concurrency [] = true.
  Proof.
    reflexivity.
  Qed.

  Example CC_inr_nil : forall h, check_concurrency [(h, inr [])] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_one_I :
    forall h i,
      check_concurrency [(h, inl (ClientRequest 0 0 i))] = true.
  Proof.
    reflexivity.
  Qed.

  Example CC_one_IO_true :
    forall h i o,
      check_concurrency [(h, inl (ClientRequest 0 0 i)); (h, inr [ClientResponse 0 0 o])] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_concurrent_request_false :
    forall h i o,
      check_concurrency [(h, inl (ClientRequest 0 0 i));
                         (h, inl (ClientRequest 0 1 i));
                         (h, inr [ClientResponse 0 0 o])] = false.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_old_request_true :
    forall h i o,
      check_concurrency [(h, inl (ClientRequest 0 1 i));
                         (h, inl (ClientRequest 0 0 i));
                         (h, inr [ClientResponse 0 0 o])] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_dup_request_true :
    forall h i o,
      check_concurrency [(h, inl (ClientRequest 0 0 i));
                         (h, inl (ClientRequest 0 0 i));
                         (h, inr [ClientResponse 0 0 o])] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_dup_request_true_2 :
    forall h i o,
      check_concurrency [(h, inl (ClientRequest 0 0 i));
                         (h, inr [ClientResponse 0 0 o]);
                         (h, inl (ClientRequest 0 0 i))] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_two_clients_serialized :
    forall h h' i i' o o',
      check_concurrency [(h, inl (ClientRequest 0 0 i));
                         (h, inr [ClientResponse 0 0 o]);
                         (h', inl (ClientRequest 1 0 i'));
                         (h', inr [ClientResponse 1 0 o'])] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Example CC_two_clients_interleaved :
    forall h h' i i' o o',
      check_concurrency [(h, inl (ClientRequest 0 0 i));
                         (h', inl (ClientRequest 1 0 i'));
                         (h, inr [ClientResponse 0 0 o]);
                         (h', inr [ClientResponse 1 0 o'])] = true.
  Proof.
    intros.
    reflexivity.
  Qed.

  Definition input_correct (tr : list (name * (raft_input + list raft_output))) : Prop :=
    check_concurrency tr = true.

  Lemma input_correct_snoc_inv :
    forall tr ev,
      input_correct (tr ++ [ev]) -> input_correct tr.
  Proof.
    unfold input_correct, check_concurrency.
    intros.
    eauto using check_concurrency'_snoc_inv.
  Qed.
End RaftLinearizableDefinitions.