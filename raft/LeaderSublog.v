Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import Raft.
Require Import VerdiTactics.
Require Import CommonTheorems.
Require Import OneLeaderPerTerm.

Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.


Section LeaderSublog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Ltac prove_in :=
    match goal with
      | [ _ : nwPackets ?net = _,
              _ : In (?p : packet) _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition)
      | [ _ : nwPackets ?net = _,
              _ : pBody ?p = _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; intuition)
    end.


  Definition leader_sublog_host_invariant (net : network) :=
    forall leader e h,
      type (nwState net leader) = Leader ->
      In e (log (nwState net h)) ->
      eTerm e = currentTerm (nwState net leader) ->
      In e (log (nwState net leader)).

  Definition leader_sublog_nw_invariant (net : network) :=
    forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
      type (nwState net leader) = Leader ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm
                              entries leaderCommit ->
      In e entries ->
      eTerm e = currentTerm (nwState net leader) ->
      In e (log (nwState net leader)).

  Definition leader_sublog_invariant (net : network) :=
    leader_sublog_host_invariant net /\
    leader_sublog_nw_invariant net.

  Notation is_append_entries m :=
    (exists t n prevT prevI entries c,
       m = AppendEntries t n prevT prevI entries c).

  Lemma leader_sublog_invariant_same_state :
    forall net net',
      leader_sublog_host_invariant net ->
      (forall h, log (nwState net h) = log (nwState net' h)) ->
      (forall h, type (nwState net' h) = Leader ->
            type (nwState net h) = Leader /\
            currentTerm (nwState net h) = currentTerm (nwState net' h)) ->
      leader_sublog_host_invariant net'.
  Proof.
    unfold leader_sublog_host_invariant in *. intros.
    specialize (H leader e h).
    forward H; [apply H1; auto|].
    intuition.
    rewrite H0 in *. specialize (H1 leader). intuition.
    rewrite H7 in *; auto.
    rewrite H0 in *. auto.
  Qed.

  Lemma leader_sublog_invariant_subset :
    forall net net',
      leader_sublog_invariant net ->
      (forall p, is_append_entries (pBody p) -> In p (nwPackets net') -> In p (nwPackets net)) ->
      (forall h, log (nwState net h) = log (nwState net' h)) ->
      (forall h, type (nwState net' h) = Leader ->
            type (nwState net h) = Leader /\
            currentTerm (nwState net h) = currentTerm (nwState net' h)) ->
      leader_sublog_invariant net'.
  Proof.
    unfold leader_sublog_invariant in *. intros; intuition.
    - eauto using leader_sublog_invariant_same_state.
    - unfold leader_sublog_nw_invariant in *. intros.
      pose proof H1 leader.
      pose proof H2 leader; concludes.
      pose proof H3 leader. intuition.
      symmetry in H13. 
      repeat find_rewrite.
      eapply H11; simpl in *; repeat find_rewrite; eauto.
      assert (is_append_entries (pBody p)) by (repeat eexists; eauto).
      eauto.
  Qed.

  Theorem leader_sublog_do_leader :
    raft_net_invariant_do_leader leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_do_leader.
    intros.
    unfold doLeader in *.
    break_match; try solve [
                       find_inversion; simpl in *;
                       eapply leader_sublog_invariant_subset;
                       eauto; intuition; simpl in *;
                       repeat find_apply_hyp_hyp; intuition;
                       repeat find_higher_order_rewrite; repeat break_if; subst; intuition].
    break_if.
    - unfold replicaMessage in *. find_inversion. simpl in *.
      unfold leader_sublog_invariant in *; intuition.
      + unfold leader_sublog_host_invariant in *. intros.
        simpl in *. repeat find_higher_order_rewrite.
        repeat break_if; simpl in *; intuition eauto.
      + unfold leader_sublog_nw_invariant in *. intros.
        simpl in *. repeat find_higher_order_rewrite.
        find_apply_hyp_hyp.
        break_if; intuition idtac; simpl in *; subst; intuition eauto;
        simpl in *;
        repeat do_in_map; subst; simpl in *;
        find_inversion; eauto using findGtIndex_in.
    - find_inversion.
      unfold leader_sublog_invariant, leader_sublog_nw_invariant,
      leader_sublog_host_invariant, advanceCommitIndex in *.

      intuition; find_higher_order_rewrite; repeat break_if; simpl in *; subst;
      repeat break_if; simpl in *; eauto;
      find_apply_hyp_hyp; intuition; eauto.
  Qed.

  Lemma leader_sublog_client_request :
    raft_net_invariant_client_request leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_client_request.
    intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, handleClientRequest in *. intuition idtac.
    - break_match; find_inversion; simpl in *; repeat find_higher_order_rewrite;
      repeat break_if; subst; simpl in *;
      intuition eauto;
      simpl in *; in_crush_finish; intuition eauto. in_crush; eauto.
      exfalso.
      match goal with
        | H : raft_intermediate_reachable _ |- _ =>
          apply one_leader_per_term_invariant in H
      end.
      assert (leader = h) by (eapply_prop one_leader_per_term; eauto).
      intuition.
    - break_match; find_inversion; simpl in *; repeat find_higher_order_rewrite;
      repeat break_if; find_apply_hyp_hyp; intuition eauto; subst.
      simpl in *.
      in_crush; eauto.
  Qed.

  Lemma leader_sublog_timeout :
    raft_net_invariant_timeout
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_timeout. intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, handleTimeout, tryToBecomeLeader in *.
    intuition idtac; simpl in *.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto; solve_by_inversion.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto;
      find_apply_hyp_hyp; intuition eauto; try solve_by_inversion;
      in_crush; repeat find_inversion; discriminate.
  Qed.

  Lemma leader_sublog_append_entries :
    raft_net_invariant_append_entries
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_append_entries. intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, handleAppendEntries, advanceCurrentTerm in *.
    intuition idtac; simpl in *.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto; try solve_by_inversion;
      do_in_app; intuition; eauto using removeAfterIndex_in.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto;
      find_apply_hyp_hyp; intuition eauto; subst; try discriminate.
  Qed.

  Lemma leader_sublog_append_entries_reply :
    raft_net_invariant_append_entries_reply
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_append_entries_reply. intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, handleAppendEntriesReply, advanceCurrentTerm in *.
    intuition idtac; simpl in *.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto; try solve_by_inversion.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto;
      find_apply_hyp_hyp; intuition eauto; try discriminate.
  Qed.

  Lemma leader_sublog_request_vote :
    raft_net_invariant_request_vote
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_request_vote. intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, handleRequestVote, advanceCurrentTerm in *.
    intuition idtac; simpl in *.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto; try solve_by_inversion.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto;
      find_apply_hyp_hyp; intuition eauto; subst; try discriminate.
  Qed.

  Lemma leader_sublog_request_vote_reply :
    raft_net_invariant_request_vote_reply
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_request_vote_reply.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
           leader_sublog_host_invariant, handleRequestVoteReply, advanceCurrentTerm.
    intuition idtac; simpl in *.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *; intuition eauto; try discriminate.
      + admit. (* these will use the new invariant *)
      + admit.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *; intuition eauto;
      find_apply_hyp_hyp; intuition eauto; subst; try discriminate.
      + admit.
      + admit.
  Admitted.
  
  Lemma leader_sublog_do_generic_server :
    raft_net_invariant_do_generic_server
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_do_generic_server.
    intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, doGenericServer, applyEntries in *.
    intuition idtac; simpl in *.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto; try solve_by_inversion.
    - repeat find_higher_order_rewrite; repeat break_match; repeat find_inversion;
      subst; simpl in *;
      intuition eauto;
      find_apply_hyp_hyp; intuition eauto; subst; try discriminate.
  Qed.
  
  Lemma leader_sublog_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset.
    intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant in *. intuition idtac;
      repeat find_reverse_higher_order_rewrite; intuition eauto.
  Qed.

  Lemma leader_sublog_reboot :
    raft_net_invariant_reboot
      leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_reboot. intros.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant,
    leader_sublog_host_invariant, reboot in *. intuition idtac.
    - repeat find_higher_order_rewrite.
      simpl in *. repeat break_match; subst; simpl in *; intuition eauto; discriminate.
    - repeat find_higher_order_rewrite.
      simpl in *. repeat find_rewrite.
      repeat break_match; subst; simpl in *;
      intuition eauto; try discriminate.
  Qed.

  Theorem leader_sublog_init :
    raft_net_invariant_init leader_sublog_invariant.
  Proof.
    unfold raft_net_invariant_init, leader_sublog_invariant,
    leader_sublog_host_invariant, leader_sublog_nw_invariant;
    intuition.
  Qed.
    
  Theorem leader_sublog_invariant_invariant :
    forall net,
      raft_intermediate_reachable net ->
      leader_sublog_invariant net.
  Proof.
    intros.
    eapply raft_net_invariant; eauto.
    - apply leader_sublog_init.
    - apply leader_sublog_client_request.
    - apply leader_sublog_timeout.
    - apply leader_sublog_append_entries.
    - apply leader_sublog_append_entries_reply.
    - apply leader_sublog_request_vote.
    - apply leader_sublog_request_vote_reply.
    - apply leader_sublog_do_leader.
    - apply leader_sublog_do_generic_server.
    - apply leader_sublog_state_same_packet_subset.
    - apply leader_sublog_reboot.
  Qed.
  
End LeaderSublog.
