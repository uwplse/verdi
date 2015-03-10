Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section AllEntriesVotesWithLog.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition all_entries_votes_with_log net :=
    forall t e h t' leader l,
      In (t, e) (allEntries (fst (nwState net h))) ->
      In (t', leader, l) (votesWithLog (fst (nwState net h))) ->
      (exists t'' e',
         t'' > t /\
         t'' < t' /\
         In (t'', e') (allEntries (fst (nwState net h)))) \/
      In e l.

  Class all_entries_votes_with_log_interface : Prop :=
    {
      all_entries_votes_with_log_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          all_entries_votes_with_log net
    }.
End AllEntriesVotesWithLog.
