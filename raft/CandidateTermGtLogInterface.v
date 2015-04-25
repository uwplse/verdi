Require Import List.

Require Import Net.
Require Import Raft.

Section CandidateTermGtLogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition candidate_term_gt_log net :=
    forall (h : name),
      type (nwState net h) = Candidate ->
      (forall e, In e (log (nwState net h)) -> currentTerm (nwState net h) > eTerm e).

  Class candidate_term_gt_log_interface : Prop :=
    {
      candidate_term_gt_log_invariant :
        forall net,
          raft_intermediate_reachable net ->
          candidate_term_gt_log net
    }.
End CandidateTermGtLogInterface.