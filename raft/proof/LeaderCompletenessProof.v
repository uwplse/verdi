Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Sumbool.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import RaftRefinementInterface.
Require Import LeaderCompletenessInterface.
Require Import AllEntriesLeaderLogsInterface.

Section LeaderCompleteness.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {aelli : all_entries_leader_logs_interface}.
  

  Fixpoint contradicting_leader_logs_on_leader l t e :=
    match l with
      | (t', log') :: l' =>
        if (sumbool_and _ _ _ _
                        (lt_dec t t')
                        (sumbool_not _ _
                                     (in_dec entry_eq_dec e log'))) then
          (t', log') :: contradicting_leader_logs_on_leader l' t e
        else
          contradicting_leader_logs_on_leader l' t e
      | [] => []
    end.
  
  Fixpoint contradicting_leader_logs net nodes t e : list (term * name * list entry) :=
    match nodes with
      | h :: nodes' => (map (fun l => (fst l, h, snd l))
                           (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e))
                        ++ contradicting_leader_logs net nodes' t e
      | [] => []
    end.

  Definition minimal_contradicting_leader_log net t e :=
    argmin (fun l => fst (fst l)) (contradicting_leader_logs net nodes t e).

  Lemma contradicting_leader_logs_on_leader_empty :
    forall l t e,
      contradicting_leader_logs_on_leader l t e = [] ->
      forall t' log,
        In (t', log) l ->
        t' > t ->
        In e log.
  Proof.
    induction l; intros; simpl in *; intuition; subst;
    repeat break_match; subst; simpl in *; intuition eauto;
    congruence.
  Qed.

  Lemma contradicting_leader_logs_empty :
    forall net nodes t e,
      contradicting_leader_logs net nodes t e = [] ->
      forall h,
        In h nodes ->
        contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e = [].
  Proof.
    intros.
    induction nodes; simpl in *; intuition; subst;
    find_apply_lem_hyp app_eq_nil; intuition;
    find_apply_lem_hyp map_eq_nil; auto.
  Qed.

  Lemma minimal_contradicting_leader_log_None :
    forall net t e,
      minimal_contradicting_leader_log net t e = None ->
      forall t' log h,
        In (t', log) (leaderLogs (fst (nwState net h))) ->
        t' > t ->
        In e log.
  Proof.
    intros.
    find_apply_lem_hyp argmin_None.
    eapply contradicting_leader_logs_on_leader_empty; eauto.
    eapply contradicting_leader_logs_empty; eauto.
    apply all_fin_all.
  Qed.

  Lemma In_contradicting_logs_on_leader_elim :
    forall l t e t' l',
      In (t', l') (contradicting_leader_logs_on_leader l t e) ->
      In (t', l') l /\ t < t' /\ ~ In e l'.
  Proof.
    intros; induction l; simpl in *; intuition;
    repeat break_match; subst; simpl in *; intuition;
    find_inversion; intuition.
  Qed.

  Lemma minimal_contradicting_leader_log_elim :
    forall net t e t' h l,
      minimal_contradicting_leader_log net t e = Some (t', h, l) ->
      (In (t', l) (leaderLogs (fst (nwState net h))) /\
       ~ In e l /\
       (forall h' t'' l',
          In (t'', l') (leaderLogs (fst (nwState net h'))) ->
          (t'' <= t \/
           t'' >= t' \/
           In e l'))).
  Proof.
  Admitted.

  Theorem leader_completeness_directly_committed_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_completeness_directly_committed net.
  Proof.
    unfold leader_completeness_directly_committed in *.
    intros.
    unfold directly_committed in *.
    destruct (minimal_contradicting_leader_log net (eTerm e) e) eqn:?;
             eauto using minimal_contradicting_leader_log_None.
    exfalso.
    repeat destruct p.
    find_copy_apply_lem_hyp minimal_contradicting_leader_log_elim.
  Admitted.
  
  Lemma leader_completeness_init :
    refined_raft_net_invariant_init leader_completeness.
  Admitted.

  Lemma leader_completeness_client_request :
    refined_raft_net_invariant_client_request leader_completeness.
  Admitted.

  Lemma leader_completeness_timeout :
    refined_raft_net_invariant_timeout leader_completeness.
  Admitted.

  Lemma leader_completeness_append_entries :
    refined_raft_net_invariant_append_entries leader_completeness.
  Admitted.

  Lemma leader_completeness_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leader_completeness.
  Admitted.

  Lemma leader_completeness_request_vote :
    refined_raft_net_invariant_request_vote leader_completeness.
  Admitted.

  Lemma leader_completeness_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leader_completeness.
  Admitted.

  Lemma leader_completeness_do_leader :
    refined_raft_net_invariant_do_leader leader_completeness.
  Admitted.

  Lemma leader_completeness_do_generic_server :
    refined_raft_net_invariant_do_generic_server leader_completeness.
  Admitted.

  Lemma leader_completeness_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leader_completeness.
  Admitted.

  Lemma leader_completeness_reboot :
    refined_raft_net_invariant_reboot leader_completeness.
  Admitted.

  Theorem leader_completeness_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leader_completeness net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leader_completeness_init.
    - apply leader_completeness_client_request.
    - apply leader_completeness_timeout.
    - apply leader_completeness_append_entries.
    - apply leader_completeness_append_entries_reply.
    - apply leader_completeness_request_vote.
    - apply leader_completeness_request_vote_reply.
    - apply leader_completeness_do_leader.
    - apply leader_completeness_do_generic_server.
    - apply leader_completeness_state_same_packet_subset.
    - apply leader_completeness_reboot.
  Qed.

  Instance lci :  leader_completeness_interface.
  Proof.
    split.
    exact leader_completeness_invariant.
  Qed.
End LeaderCompleteness.
