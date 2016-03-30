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

  Definition state_machine_safety_nw net :=
    forall h p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      t >= currentTerm (nwState net h) ->
      commit_recorded net h e ->
      (prevLogIndex > eIndex e \/
       (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/
       eIndex e > maxIndex entries \/
       In e entries).

  Definition state_machine_safety net :=
    state_machine_safety_host net /\ state_machine_safety_nw net.

  Class state_machine_safety_interface : Prop :=
    {
      state_machine_safety_invariant :
        forall net,
          raft_intermediate_reachable net ->
          state_machine_safety net
    }.

End StateMachineSafety.
         
