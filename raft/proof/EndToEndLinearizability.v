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

Require Import LeaderCompletenessInterface.
Require Import LeaderCompletenessProof.

Require Import AllEntriesLeaderLogsInterface.
Require Import AllEntriesLeaderLogsProof.

Require Import CommitRecordedCommittedInterface.

Require Import LeaderLogsTermSanityInterface.
Require Import LeaderLogsTermSanityProof.

Require Import LeaderLogsPreservedInterface.
Require Import LeaderLogsPreservedProof.

Require Import PrefixWithinTermInterface.
Require Import PrefixWithinTermProof.

Require Import EveryEntryWasCreatedInterface.
Require Import EveryEntryWasCreatedProof.

Require Import LeaderLogsVotesWithLogInterface.
Require Import LeaderLogsVotesWithLogProof.

Require Import AllEntriesVotesWithLogInterface.
Require Import AllEntriesVotesWithLogProof.

Require Import VotesWithLogSortedInterface.
Require Import VotesWithLogSortedProof.

Require Import TermsAndIndicesFromOneInterface.
Require Import TermsAndIndicesFromOneProof.

Require Import LeaderLogsLogMatchingInterface.
Require Import LeaderLogsLogMatchingProof.

Require Import LeaderLogsLogMatchingInterface.
Require Import LeaderLogsLogMatchingProof.

Require Import StateMachineSafetyPrimeInterface.
Require Import StateMachineSafetyPrimeProof.

Require Import AppendEntriesRequestLeaderLogsInterface.
Require Import AppendEntriesRequestLeaderLogsProof.

Require Import LeaderLogsSortedInterface.
Require Import LeaderLogsSortedProof.

Require Import LeaderLogsContiguousInterface.
Require Import LeaderLogsContiguousProof.

Require Import LogsLeaderLogsInterface.
Require Import LogsLeaderLogsProof.

Require Import OneLeaderLogPerTermInterface.
Require Import OneLeaderLogPerTermProof.

Require Import LeaderLogsSublogInterface.
Require Import LeaderLogsSublogProof.

Require Import LeadersHaveLeaderLogsInterface.
Require Import LeadersHaveLeaderLogsProof.

Require Import LeadersHaveLeaderLogsStrongInterface.
Require Import LeadersHaveLeaderLogsStrongProof.

Require Import NextIndexSafetyInterface.
Require Import NextIndexSafetyProof.

Require Import RefinedLogMatchingLemmasInterface.
Require Import RefinedLogMatchingLemmasProof.

Require Import LeaderLogsCandidateEntriesInterface.
Require Import LeaderLogsCandidateEntriesProof.

Require Import AllEntriesLogMatchingInterface.
Require Import AllEntriesLogMatchingProof.

Require Import AppendEntriesRequestTermSanityInterface.
Require Import AppendEntriesRequestTermSanityProof.

Require Import AllEntriesLeaderSublogInterface.
Require Import AllEntriesLeaderSublogProof.

Require Import LastAppliedCommitIndexMatchingInterface.
Require Import LastAppliedCommitIndexMatchingProof.

Require Import AllEntriesLeaderLogsTermInterface.
Require Import AllEntriesLeaderLogsTermProof.

Require Import StateMachineCorrectInterface.
Require Import StateMachineCorrectProof.

Require Import OutputGreatestIdInterface.
Require Import OutputGreatestIdProof.

Require Import CurrentTermGtZeroInterface.
Require Import CurrentTermGtZeroProof.

Require Import TermsAndIndicesFromOneLogInterface.
Require Import TermsAndIndicesFromOneLogProof.

Require Import TermsAndIndicesFromOneInterface.
Require Import TermsAndIndicesFromOneProof.

Require Import CandidateTermGtLogInterface.
Require Import CandidateTermGtLogProof.

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
Hint Extern 4 (@leaderLogs_term_sanity_interface _ _ _) => apply lltsi : typeclass_instances.
Hint Extern 4 (@leaderLogs_preserved_interface _ _ _) => apply llpi : typeclass_instances.
Hint Extern 4 (@prefix_within_term_interface _ _ _) => apply pwti : typeclass_instances.
Hint Extern 4 (@every_entry_was_created_interface _ _ _) => apply eewci : typeclass_instances.
Hint Extern 4 (@leaderLogs_votesWithLog_interface _ _ _) => apply llvwli : typeclass_instances.
Hint Extern 4 (@allEntries_votesWithLog_interface _ _ _) => apply aevwli : typeclass_instances.
Hint Extern 4 (@votesWithLog_sorted_interface _ _ _) => apply vwlsi : typeclass_instances.
Hint Extern 4 (@terms_and_indices_from_one_interface _ _ _) => apply taifoi : typeclass_instances.
Hint Extern 4 (@leaderLogs_entries_match_interface _ _ _) => apply lllmi : typeclass_instances.
Hint Extern 4 (@state_machine_safety'interface _ _ _) => apply sms'i : typeclass_instances.
Hint Extern 4 (@append_entries_leaderLogs_interface _ _ _) => apply aerlli : typeclass_instances.
Hint Extern 4 (@leaderLogs_sorted_interface _ _ _) => apply llsi : typeclass_instances.
Hint Extern 4 (@leaderLogs_contiguous_interface _ _ _) => apply llci : typeclass_instances.
Hint Extern 4 (@logs_leaderLogs_interface _ _ _) => apply llli : typeclass_instances.
Hint Extern 4 (@one_leaderLog_per_term_interface _ _ _) => apply ollpti : typeclass_instances.
Hint Extern 4 (@leaderLogs_sublog_interface _ _ _) => apply llsli : typeclass_instances.
Hint Extern 4 (@leaders_have_leaderLogs_interface _ _ _) => apply lhlli : typeclass_instances.
Hint Extern 4 (@leaders_have_leaderLogs_strong_interface _ _ _) => apply lhllsi : typeclass_instances.
Hint Extern 4 (@nextIndex_safety_interface _ _ _) => apply nisi : typeclass_instances.
Hint Extern 4 (@refined_log_matching_lemmas_interface _ _ _) => apply rlmli : typeclass_instances.
Hint Extern 4 (@leaderLogs_candidate_entries_interface _ _ _) => apply llcei : typeclass_instances.
Hint Extern 4 (@allEntries_log_matching_interface _ _ _) => apply aelmi : typeclass_instances.
Hint Extern 4 (@append_entries_request_term_sanity_interface _ _ _) => apply aertsi : typeclass_instances.
Hint Extern 4 (@allEntries_leader_sublog_interface _ _ _) => apply aelsi : typeclass_instances.
Hint Extern 4 (@lastApplied_commitIndex_match_interface _ _ _) => apply lacimi : typeclass_instances.
Hint Extern 4 (@allEntries_leaderLogs_term_interface _ _ _) => apply aellti : typeclass_instances.
Hint Extern 4 (@state_machine_correct_interface _ _ _) => apply smci : typeclass_instances.
Hint Extern 4 (@output_greatest_id_interface _ _ _) => apply ogii : typeclass_instances.
Hint Extern 4 (@current_term_gt_zero_interface _ _ _) => apply ctgzi : typeclass_instances.
Hint Extern 4 (@terms_and_indices_from_one_log_interface _ _ _) => apply taifoli : typeclass_instances.
Hint Extern 4 (@terms_and_indices_from_one_interface _ _ _) => apply taifoi : typeclass_instances.
Hint Extern 4 (@candidate_term_gt_log_interface _ _ _) => apply ctgli : typeclass_instances.

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
