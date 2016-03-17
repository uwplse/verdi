Require Import List.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.
Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import RefinementSpecLemmas.
Require Import SpecLemmas.

Require Import AllEntriesLeaderLogsTermInterface.
Require Import AppendEntriesRequestLeaderLogsInterface.

Section AllEntriesLeaderLogsTerm.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Context {aerlli : append_entries_leaderLogs_interface}.

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

  Lemma allEntries_leaderLogs_term_append_entries :
    refined_raft_net_invariant_append_entries allEntries_leaderLogs_term.
  Proof.
    red. unfold allEntries_leaderLogs_term. intros. simpl in *. subst.
    repeat find_higher_order_rewrite.
    destruct_update; simpl in *;
    [|find_apply_hyp_hyp; intuition;
      right; break_exists_exists; intuition;
      find_higher_order_rewrite;
      destruct_update; simpl in *; eauto;
      rewrite update_elections_data_appendEntries_leaderLogs; eauto].
    find_apply_lem_hyp update_elections_data_appendEntries_allEntries_term.
    intuition;
      [find_apply_hyp_hyp; intuition;
       right; break_exists_exists; intuition;
       find_higher_order_rewrite;
       destruct_update; simpl in *; eauto;
       rewrite update_elections_data_appendEntries_leaderLogs; eauto|].
    subst.
    match goal with
      | H : context [pBody] |- _ =>
        eapply append_entries_leaderLogs_invariant in H; eauto
    end.
    break_exists. break_and. subst. do_in_app.
    break_or_hyp; try find_apply_hyp_hyp; auto.
    right.
    find_eapply_lem_hyp Prefix_In; eauto.
    repeat eexists; eauto.
    find_higher_order_rewrite;
      destruct_update; simpl in *; eauto;
      rewrite update_elections_data_appendEntries_leaderLogs; subst; eauto.
  Qed.

  (* rest of cases are easy *)
  Lemma allEntries_leaderLogs_term_init :
    refined_raft_net_invariant_init allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_init, allEntries_leaderLogs_term.
    simpl. intuition.
  Qed.

  Lemma allEntries_leaderLogs_term_client_request :
    refined_raft_net_invariant_client_request allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_client_request, allEntries_leaderLogs_term.
    simpl.
    intros.
    subst.
    repeat find_higher_order_rewrite.
    destruct_update.
    - simpl in *.
      find_copy_apply_lem_hyp update_elections_data_client_request_allEntries.
      intuition.
      + repeat find_rewrite.
        find_apply_hyp_hyp.
        intuition.
        right.
        break_exists_exists.
        find_higher_order_rewrite.
        destruct_update.
        * simpl in *. rewrite update_elections_data_client_request_leaderLogs.
          intuition.
        * intuition.
      + break_exists. intuition.
        find_rewrite. simpl in *. intuition.
        * find_inversion.
          find_copy_apply_lem_hyp handleClientRequest_type.
          intuition.
          repeat find_rewrite. intuition.
        * find_apply_hyp_hyp.
          intuition.
          right.
          break_exists_exists.
          find_higher_order_rewrite.
          { destruct_update.
            * simpl in *. rewrite update_elections_data_client_request_leaderLogs.
              intuition.
            * intuition.
          }
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      { destruct_update.
        * simpl in *. rewrite update_elections_data_client_request_leaderLogs.
          intuition.
        * intuition.
      }
  Qed.

  Lemma allEntries_leaderLogs_term_timeout :
    refined_raft_net_invariant_timeout allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_timeout, allEntries_leaderLogs_term.
    simpl. intros.
    repeat find_higher_order_rewrite.
    destruct_update.
    - simpl in *.
      find_rewrite_lem update_elections_data_timeout_allEntries.
      find_apply_hyp_hyp.
      intuition.
      right. break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl in *. rewrite update_elections_data_timeout_leaderLogs. intuition.
      + intuition.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl in *. rewrite update_elections_data_timeout_leaderLogs. intuition.
      + intuition.
  Qed.

  Lemma allEntries_leaderLogs_term_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_append_entries_reply, allEntries_leaderLogs_term.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    destruct_update.
    - simpl in *. find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl in *. auto.
      + intuition.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl in *. auto.
      + intuition.
  Qed.

  Lemma allEntries_leaderLogs_term_request_vote :
    refined_raft_net_invariant_request_vote allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_request_vote, allEntries_leaderLogs_term.
    simpl.
    intros.
    repeat find_higher_order_rewrite.
    destruct_update.
    - simpl in *. find_rewrite_lem update_elections_data_requestVote_allEntries.
      find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl in *. rewrite leaderLogs_update_elections_data_requestVote. auto.
      + intuition.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl in *. rewrite leaderLogs_update_elections_data_requestVote. auto.
      + intuition.
  Qed.

  Lemma allEntries_leaderLogs_term_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_request_vote_reply, allEntries_leaderLogs_term.
    simpl. intros.
    repeat find_higher_order_rewrite.
    destruct_update.
    - simpl in *. find_rewrite_lem update_elections_data_requestVoteReply_allEntries.
      find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl. intuition.
        apply update_elections_data_requestVoteReply_old.
        auto.
      + auto.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl. intuition.
        apply update_elections_data_requestVoteReply_old.
        auto.
      + auto.
  Qed.

  Lemma allEntries_leaderLogs_term_do_leader :
    refined_raft_net_invariant_do_leader allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_do_leader, allEntries_leaderLogs_term.
    simpl. intros.
    repeat find_higher_order_rewrite.
    match goal with
    | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] =>
      ((replace gd with (fst (nwState net h)) in * by (now rewrite H));
        (replace d with (snd (nwState net h)) in * by (now rewrite H))); clear H
    end.
    destruct_update.
    - simpl in *.
      find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update; auto.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      repeat find_higher_order_rewrite.
      destruct_update; auto.
  Qed.

  Lemma allEntries_leaderLogs_term_do_generic_server :
    refined_raft_net_invariant_do_generic_server allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_do_generic_server, allEntries_leaderLogs_term.
    simpl. intros.
    repeat find_higher_order_rewrite.
    match goal with
    | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] =>
      ((replace gd with (fst (nwState net h)) in * by (now rewrite H));
        (replace d with (snd (nwState net h)) in * by (now rewrite H))); clear H
    end.
    destruct_update.
    - simpl in *.
      find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update; auto.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      repeat find_higher_order_rewrite.
      destruct_update; auto.
  Qed.

  Lemma allEntries_leaderLogs_term_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_state_same_packet_subset, allEntries_leaderLogs_term.
    simpl.
    intros.
    find_reverse_higher_order_rewrite.
    find_apply_hyp_hyp.
    intuition.
    right. break_exists_exists.
    find_reverse_higher_order_rewrite.
    auto.
  Qed.

  Lemma allEntries_leaderLogs_term_reboot :
    refined_raft_net_invariant_reboot allEntries_leaderLogs_term.
  Proof.
    unfold refined_raft_net_invariant_reboot, allEntries_leaderLogs_term.
    simpl. intros.
    find_higher_order_rewrite.
    match goal with
    | [ H : nwState ?net ?h = (?gd, ?d) |- _ ] =>
      ((replace gd with (fst (nwState net h)) in * by (now rewrite H));
        (replace d with (snd (nwState net h)) in * by (now rewrite H))); clear H
    end.
    subst.
    destruct_update.
    - simpl in *.
      find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl. intuition.
      + auto.
    - find_apply_hyp_hyp.
      intuition.
      right.
      break_exists_exists.
      find_higher_order_rewrite.
      destruct_update.
      + simpl. intuition.
      + auto.
  Qed.

  Lemma allEntries_leaderLogs_term_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      allEntries_leaderLogs_term net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - apply allEntries_leaderLogs_term_init.
    - apply allEntries_leaderLogs_term_client_request.
    - apply allEntries_leaderLogs_term_timeout.
    - apply allEntries_leaderLogs_term_append_entries.
    - apply allEntries_leaderLogs_term_append_entries_reply.
    - apply allEntries_leaderLogs_term_request_vote.
    - apply allEntries_leaderLogs_term_request_vote_reply.
    - apply allEntries_leaderLogs_term_do_leader.
    - apply allEntries_leaderLogs_term_do_generic_server.
    - apply allEntries_leaderLogs_term_state_same_packet_subset.
    - apply allEntries_leaderLogs_term_reboot.
  Qed.

  Instance aellti : allEntries_leaderLogs_term_interface.
  split.
  exact allEntries_leaderLogs_term_invariant.
  Qed.
End AllEntriesLeaderLogsTerm.
