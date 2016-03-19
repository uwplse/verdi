Require Import Raft.
Require Import RaftRefinementInterface.
Require Import SpecLemmas.
Require Import RefinementSpecLemmas.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import VotesWithLogTermSanityInterface.

Section VotesWithLogTermSanity.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rri : raft_refinement_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Ltac start :=
    red; unfold votesWithLog_term_sanity; simpl; intros.

  Ltac start_update :=
    start;
    repeat find_higher_order_rewrite;
    update_destruct; subst; rewrite_update; [|eauto].

  Lemma votesWithLog_term_sanity_cases :
    forall net st' ps' h gd d,
      votesWithLog_term_sanity net ->
      (forall h' : Net.name, st' h' = update (nwState net) h (gd, d) h') ->
      (forall t' h' l',
        In (t', h', l') (votesWithLog gd) ->
        In (t', h', l') (votesWithLog (fst (nwState net h))) \/
        (t' = currentTerm d /\ l' = log d)) ->
      currentTerm d >= currentTerm (snd (nwState net h)) ->
      votesWithLog_term_sanity {| nwPackets := ps'; nwState := st' |}.
  Proof.
    unfold votesWithLog_term_sanity. intros.
    find_higher_order_rewrite. update_destruct; subst; rewrite_update; [|eauto].
    simpl in *. find_apply_hyp_hyp. break_or_hyp.
    - find_apply_hyp_hyp. omega.
    - break_and. subst. auto.
  Qed.

  Ltac start_cases :=
    red; intros; eapply votesWithLog_term_sanity_cases; eauto.

  Ltac solve_votesWithLog lem :=
    intros; subst; first [
      left; solve [eapply lem; eauto] |  (* votesWithLog doesn't change *)
      solve [eapply lem; eauto]  (* has both cases *)
    ].

  Ltac solve_currentTerm lem :=
    find_apply_lem_hyp lem; solve [intuition].

  Lemma votesWithLog_term_sanity_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      votesWithLog_term_sanity net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - start. contradiction.
    - start_cases.
      + solve_votesWithLog votesWithLog_update_elections_data_client_request.
      + solve_currentTerm handleClientRequest_type.
    - start_cases.
      + solve_votesWithLog votesWithLog_update_elections_data_timeout.
      + solve_currentTerm handleTimeout_type_strong.
    - start_cases.
      + solve_votesWithLog votesWithLog_update_elections_data_append_entries.
      + solve_currentTerm handleAppendEntries_type_term.
    - start_cases.
      + intros. subst. auto.
      + solve_currentTerm handleAppendEntriesReply_type_term.
    - start_cases.
      + solve_votesWithLog votesWithLog_update_elections_data_request_vote.
      + solve_currentTerm handleRequestVote_type_term.
    - start_cases.
      + solve_votesWithLog votesWithLog_update_elections_data_request_vote_reply.
      + solve_currentTerm handleRequestVoteReply_type.
    - start_cases.
      + intros. find_rewrite. simpl. auto.
      + find_rewrite. simpl. solve_currentTerm doLeader_type.
    - start_cases.
      + intros. find_rewrite. simpl. auto.
      + find_rewrite. simpl. solve_currentTerm doGenericServer_type.
    - start. find_reverse_higher_order_rewrite. eauto.
    - start_update. unfold reboot in *. simpl in *.
      specialize (H1 t l hs h0). find_rewrite. simpl in *. eauto.
  Qed.

  Instance vwltsi : votesWithLog_term_sanity_interface.
    split. apply votesWithLog_term_sanity_invariant.
  Defined.

End VotesWithLogTermSanity.
