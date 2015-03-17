Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.
Require Import Sorting.Permutation.


Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import Raft.
Require Import CommonTheorems.
Require Import TraceUtil.
Require Import Linearizability.

Require Import RaftLinearizableProofs.

Require Import OutputCorrectInterface.
Require Import OutputCorrectProof.

Require Import InputBeforeOutputInterface.
Require Import InputBeforeOutputProof.

Require Import CausalOrderPreservedInterface.
Require Import CausalOrderPreservedProof.

Require Import AppliedImpliesInputInterface.
Require Import AppliedImpliesInputProof.

Require Import OutputImpliesAppliedInterface.
Require Import OutputImpliesAppliedProof.

Require Import LogMatchingInterface.
Require Import LogMatchingProof.

Require Import SortedInterface.
Require Import SortedProof.

Require Import TermSanityInterface.
Require Import TermSanityProof.

Require Import LeaderSublogInterface.
Require Import LeaderSublogProof.

Require Import RaftRefinementInterface.
Require Import RaftRefinementProof.

Require Import CandidateEntriesInterface.
Require Import CandidateEntriesProof.

Require Import CroniesTermInterface.
Require Import CroniesTermProof.

Require Import CroniesCorrectInterface.
Require Import CroniesCorrectProof.

Require Import VotesCorrectInterface.
Require Import VotesCorrectProof.

Require Import CandidatesVoteForSelvesInterface.
Require Import CandidatesVoteForSelvesProof.

Require Import OneLeaderPerTermInterface.
Require Import OneLeaderPerTermProof.

Require Import UniqueIndicesInterface.
Require Import UniqueIndicesProof.

Require Import AppliedEntriesMonotonicInterface.
Require Import AppliedEntriesMonotonicProof.

Require Import StateMachineSafetyInterface.
Require Import StateMachineSafetyProof.

Require Import MaxIndexSanityInterface.
Require Import MaxIndexSanityProof.

Require Import LeaderCompletenessInterface.
Require Import LeaderCompletenessProof.

Require Import AllEntriesLeaderLogsInterface.
Require Import AllEntriesLeaderLogsProof.

Require Import CommitRecordedCommittedInterface.
Require Import CommitRecordedCommittedProof.

Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
Hint Extern 4 (@raft_refinement_interface _ _ _) => apply rri : typeclass_instances.
Hint Extern 4 (@cronies_term_interface _ _ _) => apply cti : typeclass_instances.
Hint Extern 4 (@votes_correct_interface _ _ _) => apply vci : typeclass_instances.
Hint Extern 4 (@cronies_correct_interface _ _ _) => apply cci : typeclass_instances.
Hint Extern 4 (@candidates_vote_for_selves_interface _ _ _) => apply cvfsi : typeclass_instances.
Hint Extern 4 (@candidate_entries_interface _ _ _) => apply cei : typeclass_instances.
Hint Extern 4 (@one_leader_per_term_interface _ _ _) => apply olpti : typeclass_instances.
Hint Extern 4 (@leader_sublog_interface _ _ _) => apply lsi : typeclass_instances.
Hint Extern 4 (@unique_indices_interface _ _ _) => apply uii : typeclass_instances.
Hint Extern 4 (@sorted_interface _ _ _) => apply si : typeclass_instances.
Hint Extern 4 (@term_sanity_interface _ _ _) => apply tsi : typeclass_instances.
Hint Extern 4 (@log_matching_interface _ _ _) => apply lmi : typeclass_instances.
Hint Extern 4 (@applied_entries_monotonic_interface _ _ _) => apply aemi : typeclass_instances.
Hint Extern 4 (@state_machine_safety_interface _ _ _) => apply smsi : typeclass_instances.
Hint Extern 4 (@output_implies_applied_interface _ _ _) => apply oiai : typeclass_instances.
Hint Extern 4 (@applied_implies_input_interface _ _ _) => apply aiii : typeclass_instances.
Hint Extern 4 (@causal_order_preserved_interface _ _ _) => apply copi : typeclass_instances.
Hint Extern 4 (@input_before_output_interface _ _ _) => apply iboi : typeclass_instances.
Hint Extern 4 (@output_correct_interface _ _ _) => apply oci : typeclass_instances.
Hint Extern 4 (@max_index_sanity_interface _ _ _) => apply misi : typeclass_instances.
Hint Extern 4 (@leader_completeness_interface _ _ _) => apply lci : typeclass_instances.
Hint Extern 4 (@all_entries_leader_logs_interface _ _ _) => apply aelli : typeclass_instances.
Hint Extern 4 (@commit_recorded_committed_interface _ _ _) => apply crci : typeclass_instances.

Section EndToEndProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_f_star step_f_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof.
    intros.
    eapply (@raft_linearizable' orig_base_params one_node_params raft_params); eauto;
    auto with typeclass_instances.
  Qed.
End EndToEndProof.

About raft_linearizable.
Print Assumptions raft_linearizable.