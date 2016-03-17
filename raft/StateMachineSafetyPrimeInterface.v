Require Import List.
Import ListNotations.

Require Import Net.
Require Import StructTact.Util.
Require Import StructTact.StructTactics.
Require Import CommonDefinitions.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.

Section StateMachineSafety'.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition state_machine_safety_host' net :=
    forall e e' t t',
      committed net e t ->
      committed net e' t' ->
      eIndex e = eIndex e' ->
      e = e'.

  Definition state_machine_safety_nw' net :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit e t',
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      committed net e t' ->
      t >= t' ->
      (prevLogIndex > eIndex e \/
       (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/
       eIndex e > maxIndex entries \/
       In e entries).

  Definition state_machine_safety' net :=
    state_machine_safety_host' net /\ state_machine_safety_nw' net.

  Class state_machine_safety'interface : Prop :=
    {
      state_machine_safety'_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          state_machine_safety' net
    }.

End StateMachineSafety'.
