Require Import List.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import LeaderLogsPreservedInterface.

Section AllEntriesLeaderLogs.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Inductive in_any_log (net : network) (e : entry) : Prop :=
  | in_log : forall h, In e (log (snd (nwState net h))) ->
                  in_any_log net e
  | in_aer : forall p es, In p (nwPackets net) ->
                     mEntries (pBody p) = Some es ->
                     In e es ->
                     in_any_log net e
  | in_ll : forall h t ll, In (t, ll) (leaderLogs (fst (nwState net h))) ->
                      In e ll ->
                      in_any_log net e.

  Hint Constructors in_any_log.
                      

  Definition leaderLogs_preserved_in_any_log net :=
    forall h ll leader e e',
      In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) ->
      In e (log (snd (nwState net h))) ->
      In e' ll ->
      In e' (log (snd (nwState net h))).

  Definition leaderLogs_index_lt_entry net :=
    forall leader ll e e',
      in_any_log net e ->
      In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) ->
      In e' ll ->
      eIndex e > eIndex e'.

  Ltac destruct_hyp P :=
    match goal with
      | H : context [ P ] |- _ => destruct H
    end.

  Ltac invcs_hyp P :=
    match goal with
      | H : context [ P ] |- _ => invcs H
    end.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma update_elections_data_appendEntries_leaderLogs :
    forall h st t h' pli plt es ci,
      leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) =
      leaderLogs (fst st).
  Proof.
    intros.
    unfold update_elections_data_appendEntries.
    repeat break_match; subst; simpl in *; auto.
  Qed.

  Ltac prove_in :=
    match goal with
      | [ _ : nwPackets ?net = _,
              _ : In (?p : packet) _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition)
      | [ _ : nwPackets ?net = _,
              _ : pBody ?p = _ |- _] =>
        assert (In p (nwPackets net)) by (repeat find_rewrite; intuition)
    end.

  Lemma mEntries_spec :
    forall body t n pli plt es ci,
      body = AppendEntries t n pli plt es ci ->
      mEntries body = Some es.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Hint Resolve mEntries_spec.

  Hint Resolve removeAfterIndex_in.

  Lemma handleAppendEntries_in_log_in_any_log :
    forall xs p ys net t n pli plt es ci st' m e,
      nwPackets net = xs ++ p :: ys ->
      pBody p = AppendEntries t n pli plt es ci ->
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt
                          es ci = (st', m) ->
      In e (log st') ->
      in_any_log net e.
  Proof.
    intros.
    find_apply_lem_hyp handleAppendEntries_log.
    intuition; find_rewrite; try prove_in; eauto.
    do_in_app; intuition eauto.
  Qed.


  Lemma handleAppendEntries_no_m_entries :
    forall h st t n pli plt es ci st' m es',
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      ~ (mEntries m = Some es').
  Proof.
    intros.
    unfold handleAppendEntries in *.
    repeat break_match; find_inversion; simpl in *; congruence.
  Qed.
  
  Lemma leaderLogs_index_lt_entry_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_index_lt_entry.
  Proof.
    unfold refined_raft_net_invariant_append_entries, leaderLogs_index_lt_entry.
    intros. 
    invcs_hyp in_any_log.
    - find_higher_order_rewrite.
      repeat (update_destruct_hyp; subst; rewrite_update);
        simpl in *;
        try find_rewrite_lem update_elections_data_appendEntries_leaderLogs;
        eauto using handleAppendEntries_in_log_in_any_log.
    - find_higher_order_rewrite.
      find_apply_hyp_hyp.
      repeat (update_destruct_hyp; subst; rewrite_update);
        simpl in *;
        try find_rewrite_lem update_elections_data_appendEntries_leaderLogs;
        intuition eauto; subst; simpl in *; exfalso;
        eapply handleAppendEntries_no_m_entries; eauto.
    - find_higher_order_rewrite.
      repeat (update_destruct_hyp; subst; rewrite_update);
        simpl in *;
        repeat find_rewrite_lem update_elections_data_appendEntries_leaderLogs;
        eauto.
  Qed.

  Lemma leaderLogs_index_lt_entry_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_index_lt_entry.
  Admitted.
  
  Lemma leaderLogs_index_lt_entry_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_reboot :
    refined_raft_net_invariant_reboot leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_init :
    refined_raft_net_invariant_init leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_timeout :
    refined_raft_net_invariant_timeout leaderLogs_index_lt_entry.
  Admitted.

  Lemma leaderLogs_index_lt_entry_client_request :
    refined_raft_net_invariant_client_request leaderLogs_index_lt_entry.
  Admitted.
  
  Theorem leaderLogs_index_lt_entry_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_index_lt_entry net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply leaderLogs_index_lt_entry_init.
    - apply leaderLogs_index_lt_entry_client_request.
    - apply leaderLogs_index_lt_entry_timeout.
    - apply leaderLogs_index_lt_entry_append_entries.
    - apply leaderLogs_index_lt_entry_append_entries_reply.
    - apply leaderLogs_index_lt_entry_request_vote.
    - apply leaderLogs_index_lt_entry_request_vote_reply.
    - apply leaderLogs_index_lt_entry_do_leader.
    - apply leaderLogs_index_lt_entry_do_generic_server.
    - apply leaderLogs_index_lt_entry_state_same_packet_subset.
    - apply leaderLogs_index_lt_entry_reboot.
  Qed.
End AllEntriesLeaderLogs.
