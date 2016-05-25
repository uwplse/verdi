Require Import Raft.
Require Import RaftRefinementInterface.

Section CroniesCorrectInterface.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition votes_received_cronies net :=
    forall h crony,
      In crony (votesReceived (snd (nwState net h))) ->
      (type (snd (nwState net h)) = Leader \/ type (snd (nwState net h)) = Candidate) ->
      In crony (cronies (fst (nwState net h))
                        (currentTerm (snd (nwState net h)))).

  Definition cronies_votes net :=
    forall t candidate crony,
      In crony (cronies (fst (nwState net candidate)) t) ->
      In (t, candidate) (votes (fst (nwState net crony))).

  Definition votes_nw net :=
    forall p t,
      pBody p = RequestVoteReply t true ->
      In p (nwPackets net) ->
      In (t, pDst p) (votes (fst (nwState net (pSrc p)))).

  Definition votes_received_leaders net :=
    forall h,
      type (snd (nwState net h)) = Leader ->
      wonElection (dedup name_eq_dec (votesReceived (snd (nwState net h)))) = true.

  Definition cronies_correct net :=
    votes_received_cronies net /\ cronies_votes net /\ votes_nw net /\ votes_received_leaders net.

  Class cronies_correct_interface : Prop :=
    {
      cronies_correct_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          cronies_correct net
    }.
End CroniesCorrectInterface.
