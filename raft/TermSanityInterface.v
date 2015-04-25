Require Import List.

Require Import Net.
Require Import Raft.

Section TermSanityInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition no_entries_past_current_term_host net :=
    forall (h : name) e,
      In e (log (nwState net h)) ->
      eTerm e <= currentTerm (nwState net h).

  Definition no_entries_past_current_term_nw net :=
    forall e p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      In e entries ->
      eTerm e <= t.

  Definition no_entries_past_current_term net :=
    no_entries_past_current_term_host net /\
    no_entries_past_current_term_nw net.

  Class term_sanity_interface : Prop :=
    {
      no_entries_past_current_term_invariant :
        forall net,
          raft_intermediate_reachable net ->
          no_entries_past_current_term net
    }.
End TermSanityInterface.