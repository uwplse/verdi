Require Import Raft.

Require Import CommonDefinitions.

Section LogMatchingInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition log_matching_hosts (net : network) : Prop :=
    (forall h h', entries_match (log (nwState net h)) (log (nwState net h'))) /\
    (forall h i,
       1 <= i <= maxIndex (log (nwState net h)) ->
       exists e,
         eIndex e = i /\
         In e (log (nwState net h))) /\
    (forall h e,
       In e (log (nwState net h)) ->
       eIndex e > 0).


  Definition log_matching_nw (net : network) : Prop :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      (forall h e1 e2,
         In e1 entries ->
         In e2 (log (nwState net h)) ->
         eIndex e1 = eIndex e2 ->
         eTerm e1 = eTerm e2 ->
         (forall e3,
           eIndex e3 <= eIndex e1 ->
           In e3 entries ->
           In e3 (log (nwState net h))) /\
         (prevLogIndex <> 0 ->
          exists e4,
            eIndex e4 = prevLogIndex /\
            eTerm e4 = prevLogTerm /\
            In e4 (log (nwState net h)))) /\
      (forall i,
         prevLogIndex < i <= maxIndex entries ->
         exists e,
           eIndex e = i /\
           In e entries) /\
      (forall e,
         In e entries ->
         prevLogIndex < eIndex e) /\
      (forall p' t' leaderId' prevLogIndex' prevLogTerm' entries' leaderCommit',
         In p' (nwPackets net) ->
         pBody p' = AppendEntries t' leaderId' prevLogIndex' prevLogTerm' entries' leaderCommit' ->
         (forall e1 e2,
            In e1 entries ->
            In e2 entries' ->
            eIndex e1 = eIndex e2 ->
            eTerm e1 = eTerm e2 ->
            (forall e3,
               prevLogIndex' < eIndex e3 <= eIndex e1 ->
               In e3 entries ->
               In e3 entries') /\
            (forall e3,
               In e3 entries ->
               eIndex e3 = prevLogIndex' ->
               eTerm e3 = prevLogTerm') /\
            (prevLogIndex <> 0 -> prevLogIndex = prevLogIndex' -> prevLogTerm = prevLogTerm'))).

  Definition log_matching (net : network) : Prop :=
    log_matching_hosts net /\ log_matching_nw net.

  Class log_matching_interface : Prop :=
    {
      log_matching_invariant:
        forall net,
          raft_intermediate_reachable net ->
          log_matching net
    }.
End LogMatchingInterface.
