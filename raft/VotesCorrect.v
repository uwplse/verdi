Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import RaftRefinement.
Require Import VerdiTactics.

Section VotesCorrect.
  
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
      (currentTerm (snd (nwState net h)) = t /\
       votedFor (snd (nwState net h)) = Some n) ->
      In (t, n) (votes (fst (nwState net h))).


  Definition votes_le_currentTerm net :=
    forall h t n,
      In (t, n) (votes (fst (nwState net h))) ->
      t <= currentTerm (snd (nwState net h)).

  Definition votes_correct net :=
    one_vote_per_term net /\ votes_currentTerm_votedFor_correct net /\
    currentTerm_votedFor_votes_correct net /\ votes_le_currentTerm net.

  Ltac split_votes_correct :=
    intuition; [ unfold one_vote_per_term in *
               | unfold votes_currentTerm_votedFor_correct in *
               | unfold currentTerm_votedFor_votes_correct in *
               | unfold votes_le_currentTerm in *].

  Ltac start_proof :=
    simpl in *; intros; repeat find_higher_order_rewrite;
    repeat break_if; subst; simpl in *; eauto.

  Lemma votes_correct_client_request :
    refined_raft_net_invariant_client_request votes_correct.
  Proof.
    unfold refined_raft_net_invariant_client_request, votes_correct.
    split_votes_correct; start_proof;
    unfold handleClientRequest in *;
    break_match; find_inversion; simpl in *; eauto.
  Qed.
  
  Lemma votes_correct_timeout :
    refined_raft_net_invariant_timeout votes_correct.
  Proof.
    unfold refined_raft_net_invariant_timeout, votes_correct.
    split_votes_correct; start_proof;
    unfold update_elections_data_timeout, handleTimeout,
    tryToBecomeLeader in *.
    - break_let.
      repeat break_match; eauto; simpl in *;
      intuition; repeat find_inversion; eauto; simpl in *;
      try solve 
          [find_inversion;
            exfalso;
            unfold votes_le_currentTerm in *; find_apply_hyp_hyp;
            simpl in *; omega];
      try solve [unfold votes_currentTerm_votedFor_correct in *;
                  find_apply_hyp_hyp; simpl in *; find_rewrite; find_inversion; auto].
    - repeat break_match; repeat find_inversion; simpl in *; intuition eauto;
      repeat find_inversion; eauto;
      exfalso;
      unfold votes_le_currentTerm in *; find_apply_hyp_hyp;
      simpl in *; omega.
    - repeat break_match; repeat find_inversion; simpl in *; intuition eauto;
      repeat find_inversion; intuition; discriminate.
    - unfold votes_le_currentTerm in *. simpl in *.
      intros. repeat find_higher_order_rewrite.
      repeat break_if; subst; simpl in *; eauto;
      unfold update_elections_data_timeout, handleTimeout, tryToBecomeLeader in *;
      repeat break_match; repeat find_inversion; simpl in *; intuition eauto;
      find_inversion; eauto.
  Qed.

  Lemma votes_correct_append_entries :
    refined_raft_net_invariant_append_entries votes_correct.
  Proof.
    unfold refined_raft_net_invariant_append_entries, votes_correct.
    split_votes_correct; start_proof; (* solves one_vote_per_term immediately *)
    unfold update_elections_data_appendEntries, handleAppendEntries, advanceCurrentTerm in *;
    repeat break_match; repeat find_inversion; simpl in *; intuition eauto;
    try discriminate;
    try solve [unfold votes_le_currentTerm in *; find_apply_hyp_hyp; simpl in *;
               do_bool; omega];
    try solve [
          find_apply_hyp_hyp;
          unfold votes_le_currentTerm in *; find_apply_hyp_hyp; simpl in *;
          do_bool; eauto using le_antisym].
  Qed.

  Lemma votes_correct_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply votes_correct.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, votes_correct.
    split_votes_correct; start_proof; (* solves one_vote_per_term immediately *)
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    - repeat break_match; find_inversion; simpl in *; eauto;
      try solve [unfold votes_le_currentTerm in *; find_apply_hyp_hyp; simpl in *;
                 do_bool; omega];
      try solve [
            find_apply_hyp_hyp;
            unfold votes_le_currentTerm in *; find_apply_hyp_hyp; simpl in *;
            do_bool; eauto using le_antisym].
    - repeat break_match; find_inversion; simpl in *; intuition eauto;
      try discriminate.
    - repeat break_match; find_inversion; simpl in *; eauto;
      try solve [do_bool; find_apply_hyp_hyp; omega].
  Qed.

  Lemma advanceCurrentTerm_monotonic :
    forall st t,
      currentTerm st <= currentTerm (advanceCurrentTerm st t).
  Proof.
    intros. unfold advanceCurrentTerm. break_if; simpl in *; do_bool; omega.
  Qed.

  Lemma advanceCurrentTerm_le :
    forall st t t',
      t' = currentTerm (advanceCurrentTerm st t) ->
      t <= t'.
  Proof.
    intros. unfold advanceCurrentTerm in *. break_if; simpl in *; do_bool; omega.
  Qed.
  
  Lemma handleRequestVote_currentTerm_monotonic :
    forall pDst t cid lli llt d d' m,
      handleRequestVote pDst d t cid lli llt = (d', m) ->
      currentTerm d <= currentTerm d'.
  Proof.
    intros.
    unfold handleRequestVote in *.
    repeat break_match; find_inversion; subst; auto;
    simpl in *; apply advanceCurrentTerm_monotonic.
  Qed.

  Lemma handleRequestVote_votedFor :
    forall pDst t cid lli llt d d' m,
      handleRequestVote pDst d t cid lli llt = (d', m) ->
      currentTerm d = currentTerm d' ->
      votedFor d = None \/ votedFor d = votedFor d'.
  Proof.
    intros. unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; tuple_inversion; simpl in *; intuition; try discriminate;
    try solve [exfalso; do_bool; omega].
  Qed.

  Lemma handleRequestVote_currentTerm_votedFor :
    forall pDst t cid lli llt d d' m,
      handleRequestVote pDst d t cid lli llt = (d', m) ->
      (currentTerm d < currentTerm d' \/
       (currentTerm d = currentTerm d' /\ votedFor d = None) \/
       (currentTerm d = currentTerm d' /\ votedFor d = votedFor d')).
  Proof.
    intros.
    find_copy_apply_lem_hyp handleRequestVote_currentTerm_monotonic.
    find_apply_lem_hyp le_lt_or_eq. intuition.
    right. find_apply_lem_hyp handleRequestVote_votedFor; intuition.
  Qed.


  Lemma votes_correct_request_vote :
    refined_raft_net_invariant_request_vote votes_correct.
  Proof.
    unfold refined_raft_net_invariant_request_vote, votes_correct.
    split_votes_correct;
      unfold update_elections_data_requestVote in *; simpl in *;
      intros; repeat find_higher_order_rewrite;
      repeat break_match; subst; simpl in *;
      repeat find_rewrite;
      intuition eauto; 
      unfold raft_data in *; repeat find_rewrite; repeat tuple_inversion;
      find_apply_lem_hyp handleRequestVote_currentTerm_votedFor; intuition;
      try solve [
            exfalso; unfold votes_le_currentTerm in *;
            find_apply_hyp_hyp; simpl in *; unfold raft_data in *; omega|
            unfold votes_currentTerm_votedFor_correct in *;
              find_apply_hyp_hyp; simpl in *; unfold raft_data in *;
              repeat find_rewrite; discriminate|
            unfold votes_currentTerm_votedFor_correct in *;
              find_apply_hyp_hyp; simpl in *; repeat find_rewrite; find_reverse_rewrite;
              unfold raft_data in *; repeat find_rewrite;
              solve_by_inversion];
      try match goal with
            | [H : ?a < ?c |- ?b <= ?c] =>
              assert (b <= a) by eauto; omega
          end;
      solve [find_rewrite; try discriminate; repeat prove_eq; subst; intuition].
  Qed.

  Lemma handleRequestVoteReply_spec :
    forall me st src t v st',
      handleRequestVoteReply me st src t v = st' ->
      (currentTerm st' = currentTerm st /\
       votedFor st' = votedFor st) \/
      (currentTerm st < currentTerm st' /\
       votedFor st' = None).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *; repeat break_match;
    subst; do_bool; intuition.
  Qed.
  
  Lemma votes_correct_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply votes_correct.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, votes_correct.
    split_votes_correct; unfold update_elections_data_requestVoteReply in *;
    intuition.
    - repeat break_match; subst; repeat find_higher_order_rewrite;
      simpl in *; break_if; simpl in *; eauto.
    - find_apply_lem_hyp handleRequestVoteReply_spec.
      repeat break_match; subst; repeat find_higher_order_rewrite;
      simpl in *; break_if; simpl in *; eauto;
      intuition; repeat find_rewrite; eauto;
      match goal with
        | H : currentTerm _ < ?x,
              Hin : In (?x, _) _ |- _ =>
          exfalso; unfold votes_le_currentTerm in *;
          find_apply_hyp_hyp; simpl in *; unfold raft_data in *; omega
      end.
    - find_apply_lem_hyp handleRequestVoteReply_spec.
      repeat break_match; subst; repeat find_higher_order_rewrite;
      simpl in *; break_if; simpl in *; eauto;
      intuition; repeat find_rewrite; eauto; discriminate.
    - unfold votes_le_currentTerm , update_elections_data_requestVoteReply in *.
      find_apply_lem_hyp handleRequestVoteReply_spec.
      intros.
      repeat break_match; subst; repeat find_higher_order_rewrite;
      simpl in *; break_if; simpl in *; eauto;
      intuition; repeat find_rewrite; eauto;
      match goal with
        | [H : ?a < ?c |- ?b <= ?c] =>
           assert (b <= a) by eauto; omega
      end.
  Qed.

  Lemma votes_correct_do_leader :
    refined_raft_net_invariant_do_leader votes_correct.
  Proof.
    unfold refined_raft_net_invariant_do_leader, votes_correct. intros.
    assert (gd = fst (nwState net h) /\
            d = snd (nwState net h)) by (intuition; find_rewrite; reflexivity).
    match goal with H : nwState _ _ = _ |- _ => clear H end.
    split_votes_correct; unfold doLeader, advanceCommitIndex in *;
    repeat break_match; intuition;
    simpl in *; repeat find_higher_order_rewrite; repeat break_match;
    repeat find_inversion; repeat find_rewrite; simpl in *;
    intuition eauto.
  Qed.
      
  Lemma votes_correct_do_generic_server :
    refined_raft_net_invariant_do_generic_server votes_correct.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, votes_correct. intros.
    assert (gd = fst (nwState net h) /\
            d = snd (nwState net h)) by (intuition; find_rewrite; reflexivity).
    match goal with H : nwState _ _ = _ |- _ => clear H end.
    split_votes_correct; unfold doGenericServer, advanceCommitIndex in *;
    repeat break_match; intuition;
    simpl in *; repeat find_higher_order_rewrite; repeat break_match;
    repeat find_inversion; repeat find_rewrite; simpl in *;
    intuition eauto.
  Qed.

  Lemma votes_correct_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset votes_correct.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset. intros.
    unfold votes_correct in *. split_votes_correct;
      intros; repeat find_reverse_higher_order_rewrite; eauto.
  Qed.
  
  Lemma votes_correct_reboot :
    refined_raft_net_invariant_reboot votes_correct.
  Proof.
    unfold refined_raft_net_invariant_reboot. intros.
    subst.
    unfold votes_correct in *. split_votes_correct;
      intros; repeat find_higher_order_rewrite;
      simpl in *; repeat break_match; simpl in *; eauto;
      match goal with
          [ _ : nwState _ ?h = _,
                H : forall _ : name, _ |- _ ] =>
          specialize (H h)
      end; find_rewrite; simpl in *; eauto.
  Qed.

  Theorem votes_correct_init :
    refined_raft_net_invariant_init votes_correct.
  Proof.
    unfold refined_raft_net_invariant_init. unfold step_m_init.
    unfold votes_correct. split_votes_correct; simpl in *; intuition; discriminate.
  Qed.

  Theorem votes_correct_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      votes_correct net.
  Proof.
    intros.
    eapply refined_raft_net_invariant; eauto.
    - apply votes_correct_init.
    - apply votes_correct_client_request.
    - apply votes_correct_timeout.
    - apply votes_correct_append_entries.
    - apply votes_correct_append_entries_reply.
    - apply votes_correct_request_vote.
    - apply votes_correct_request_vote_reply.
    - apply votes_correct_do_leader.
    - apply votes_correct_do_generic_server.
    - apply votes_correct_state_same_packet_subset.
    - apply votes_correct_reboot.
  Qed.
End VotesCorrect.
