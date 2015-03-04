Require Import List.
Import ListNotations.
Require Import Arith.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import Raft.
Require Import CommonDefinitions.

Section StateMachineCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition state_machine_log net :=
    forall h,
      stateMachine (nwState net h) =
      snd (execute_log (deduplicate_log (removeAfterIndex (log (nwState net h))
                                                          (lastApplied (nwState net h))))).

  Definition client_cache_correct net :=
    forall h client id out,
      In (client, (id, out)) (clientCache (nwState net h)) ->
      exists e xs ys,
        eClient e = client /\
        eId e = id /\
        deduplicate_log (removeAfterIndex (log (nwState net h))
                                          (lastApplied (nwState net h))) = xs ++ e :: ys /\
        hd_error (rev (fst (execute_log (xs ++ [e])))) = Some (eInput e, out).

  Definition client_cache_complete net :=
    forall h e,
      In e (removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h))) ->
      exists id o,
        getLastId (nwState net h) (eClient e) = Some (id, o) /\
        id >= eId e.

  Definition state_machine_correct net :=
    state_machine_log net /\ client_cache_correct net /\ client_cache_complete net.

  Class state_machine_correct_interface : Prop :=
    {
      state_machine_correct_invariant :
        forall net,
          raft_intermediate_reachable net ->
          state_machine_correct net
    }.
End StateMachineCorrect.
