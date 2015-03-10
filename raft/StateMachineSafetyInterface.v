Require Import List.
Import ListNotations.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import CommonDefinitions.

Require Import Raft.

Section StateMachineSafety.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition state_machine_safety_host net :=
    forall h h' e e',
      commit_recorded net h e ->
      commit_recorded net h' e' ->
      eIndex e = eIndex e' ->
      e = e'.

  Definition maxIndex_lastApplied net :=
    forall h,
      lastApplied (nwState net h) <= maxIndex (log (nwState net h)).

  Definition maxIndex_commitIndex net :=
    forall h,
      commitIndex (nwState net h) <= maxIndex (log (nwState net h)).
  
  Definition state_machine_safety_nw net :=
    forall h p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      t >= currentTerm (nwState net h) ->
      commit_recorded net h e ->
      (prevLogIndex > eIndex e \/
       In e entries).

  Definition state_machine_safety net :=
    state_machine_safety_host net /\ state_machine_safety_nw net /\
    maxIndex_lastApplied net /\ maxIndex_commitIndex net.

  Class state_machine_safety_interface : Prop :=
    {
      state_machine_safety_invariant :
        forall net,
          raft_intermediate_reachable net ->
          state_machine_safety net
    }.

End StateMachineSafety.
         
