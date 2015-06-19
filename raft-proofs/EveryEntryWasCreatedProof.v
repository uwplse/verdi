Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import RefinementCommonDefinitions.

Require Import LeadersHaveLeaderLogsInterface.
Require Import EveryEntryWasCreatedInterface.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.
Require Import CommonTheorems.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhlli : leaders_have_leaderLogs_interface}.

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
  (* proof sketch: prove for in_any_log. the only time new entries
  come into the system is on a leader, and leaders have leaderLogs in
  their term.  *)

  Definition in_any_log_term_was_created net :=
    forall e,
      in_any_log net e ->
      term_was_created net (eTerm e).

  Ltac iae_case :=
    match goal with
      | [ H : in_any_log _ _ |- _ ] => invcs H
    end.

  Lemma term_was_created_preserved :
    forall net net' t,
      term_was_created net t ->
      (forall h t ll,
         In (t, ll) (leaderLogs (fst (nwState net h))) ->
         In (t, ll) (leaderLogs (fst (nwState net' h)))) ->
      term_was_created net' t.
  Proof.
    intros. unfold term_was_created in *.
    break_exists_exists. eauto.
  Qed.

  
  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
      | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac destruct_update :=
    repeat (first [update_destruct_hyp|update_destruct]; subst; rewrite_update).

  Ltac in_aer :=
    repeat find_rewrite; eapply in_aer; eauto; repeat find_rewrite; reflexivity.

  Lemma in_any_log_term_was_created_append_entries :
    refined_raft_net_invariant_append_entries in_any_log_term_was_created.
  Proof.
    red. intros. unfold in_any_log_term_was_created. intros.
    eapply term_was_created_preserved; [eapply_prop in_any_log_term_was_created|];
    [|
     intros; simpl in *;
     repeat find_higher_order_rewrite;
     destruct_update; simpl in *; eauto;
     rewrite update_elections_data_appendEntries_leaderLogs; eauto].
    iae_case.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_apply_lem_hyp handleAppendEntries_log. intuition; try in_aer.
      + repeat find_rewrite. eauto.
      + repeat find_rewrite. do_in_app. intuition; try in_aer.
        eauto using removeAfterIndex_in.
    - find_eapply_lem_hyp handleAppendEntries_not_append_entries.
      find_apply_hyp_hyp. intuition.
      + match goal with
          | _ : In ?p' (_ ++ _) |- _ => eapply in_aer with (p := p'); eauto
        end.
      + subst. simpl in *.
        find_false. unfold mEntries in *.
        break_match; try congruence. subst.
        repeat eexists; eauto.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
      eauto.
  Qed.

  Lemma in_any_log_term_was_created_request_vote :
    refined_raft_net_invariant_request_vote in_any_log_term_was_created.
  Proof.
    red. intros. unfold in_any_log_term_was_created. intros.
    eapply term_was_created_preserved; [eapply_prop in_any_log_term_was_created|];
    [|
     intros; simpl in *;
     repeat find_higher_order_rewrite;
     destruct_update; simpl in *; eauto;
     rewrite leaderLogs_update_elections_data_requestVote; eauto].
    iae_case.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_apply_lem_hyp handleRequestVote_log.
      repeat find_rewrite. eauto.
    - find_eapply_lem_hyp handleRequestVote_no_append_entries.
      find_apply_hyp_hyp. intuition.
      + match goal with
          | _ : In ?p' (_ ++ _) |- _ => eapply in_aer with (p := p'); eauto
        end.
      + subst. simpl in *.
        find_false. unfold mEntries in *.
        break_match; try congruence. subst.
        repeat eexists; eauto.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_rewrite_lem leaderLogs_update_elections_data_requestVote.
      eauto.
  Qed.

  Lemma in_any_log_term_was_created_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply in_any_log_term_was_created.
  Proof.
    red. intros. unfold in_any_log_term_was_created. intros.
    eapply term_was_created_preserved; [eapply_prop in_any_log_term_was_created|];
    [|
     intros; simpl in *;
     repeat find_higher_order_rewrite;
     destruct_update; simpl in *; eauto].
    iae_case.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_apply_lem_hyp handleAppendEntriesReply_log.
      repeat find_rewrite. eauto.
    - find_eapply_lem_hyp handleAppendEntriesReply_packets.
      find_apply_hyp_hyp. intuition.
      + match goal with
          | _ : In ?p' (_ ++ _) |- _ => eapply in_aer with (p := p'); eauto
        end.
      + subst. simpl in *. intuition.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
  Qed.

  Lemma in_any_log_term_was_created_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply in_any_log_term_was_created.
  Proof.
    red. intros. unfold in_any_log_term_was_created. intros.
    eapply term_was_created_preserved; [eapply_prop in_any_log_term_was_created|];
    [|intros; simpl in *;
      repeat find_higher_order_rewrite;
      destruct_update; simpl in *; eauto;
      eapply update_elections_data_requestVoteReply_old; eauto].
    iae_case.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_rewrite_lem handleRequestVoteReply_log_rewrite; eauto.
    - find_apply_hyp_hyp.
      match goal with
        | _ : In ?p' (_ ++ _) |- _ => eapply in_aer with (p := p'); eauto
      end.
    - repeat find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
      intuition; eauto. subst.
      find_rewrite_lem handleRequestVoteReply_log_rewrite. eauto.
  Qed.

  Ltac in_log_in_leader_log :=
    find_eapply_lem_hyp in_log; eapply_prop_hyp in_any_log_term_was_created in_any_log;
    unfold term_was_created in *;
    break_exists_exists;
    find_higher_order_rewrite;
    destruct_update; simpl in *; eauto;
    rewrite update_elections_data_client_request_leaderLogs; eauto.

  Lemma in_any_log_term_was_created_client_request :
    refined_raft_net_invariant_client_request in_any_log_term_was_created.
  Proof.
    red. intros. unfold in_any_log_term_was_created. intros.
    iae_case.
    - unfold term_was_created. simpl in *.
      find_higher_order_rewrite.
      destruct_update; simpl in *; eauto.
      + find_apply_lem_hyp handleClientRequest_log.
        intuition; subst; repeat find_rewrite; try in_log_in_leader_log.
        break_exists. intuition.
        repeat find_rewrite. simpl in *. intuition; subst.
        * find_eapply_lem_hyp leaders_have_leaderLogs_invariant; eauto.
          match goal with
            | [h : name |- _ ] => (exists h)
          end.
          break_exists_exists.
          repeat find_rewrite.
          repeat find_higher_order_rewrite.
          rewrite update_eq; auto. simpl.
          rewrite update_elections_data_client_request_leaderLogs.
          auto.
        * in_log_in_leader_log.
      + in_log_in_leader_log.
    -
  Admitted.
      
  Theorem in_any_log_term_was_created_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      in_any_log_term_was_created net.
  Admitted.

  Instance eewci : every_entry_was_created_interface.
  split.
  unfold every_entry_was_created. intros.
  apply in_any_log_term_was_created_invariant; eauto.
  Qed.

End EveryEntryWasCreated.
