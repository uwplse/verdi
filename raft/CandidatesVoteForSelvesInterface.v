Require Import Raft.

Section CandidatesVoteForSelvesInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Definition candidates_vote_for_selves net :=
    forall h,
      type (nwState net h) = Candidate ->
      votedFor (nwState net h) = Some h.

  Class candidates_vote_for_selves_interface : Prop :=
    {
      candidates_vote_for_selves_invariant :
        forall net,
          raft_intermediate_reachable net ->
          candidates_vote_for_selves net
    }.
End CandidatesVoteForSelvesInterface.
