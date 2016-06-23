Require Import Raft.
Require Import RaftRefinementInterface.

Section VotesCorrectInterface.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition one_vote_per_term net :=
    forall h t n n',
      In (t, n) (votes (fst (nwState net h))) ->
      In (t, n') (votes (fst (nwState net h))) ->
      n = n'.

  Definition votes_currentTerm_votedFor_correct net :=
    forall h t n,
      In (t, n) (votes (fst (nwState net h))) ->
      currentTerm (snd (nwState net h)) = t ->
      votedFor (snd (nwState net h)) = Some n.

  Definition currentTerm_votedFor_votes_correct net :=
    forall h t n,
      currentTerm (snd (nwState net h)) = t ->
       votedFor (snd (nwState net h)) = Some n ->
      In (t, n) (votes (fst (nwState net h))).

  Definition votes_correct net :=
    one_vote_per_term net /\ votes_currentTerm_votedFor_correct net /\
    currentTerm_votedFor_votes_correct net.

  Class votes_correct_interface : Prop :=
    {
      votes_correct_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          votes_correct net
    }.
End VotesCorrectInterface.
