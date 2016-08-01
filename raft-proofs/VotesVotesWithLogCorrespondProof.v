Require Import Raft.
Require Import RaftRefinementInterface.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import VotesVotesWithLogCorrespondInterface.

Section VotesVotesWithLogCorrespond.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  Context {rri : raft_refinement_interface}.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
      | [ H : context [ update _ _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.

  Lemma votes_votesWithLog_correspond_cases :
    forall net h gd d ps' st',
      votes_votesWithLog_correspond net ->
      (forall h' : Net.name, st' h' = update name_eq_dec (nwState net) h (gd, d) h') ->
      (votes gd = votes (fst (nwState net h)) /\  (* unchanged *)
       votesWithLog gd = votesWithLog (fst (nwState net h))) \/
      (exists t n l,  (* add entry *)
       votes gd = (t, n) :: votes (fst (nwState net h)) /\
       votesWithLog gd = (t, n, l) :: votesWithLog (fst (nwState net h))) ->
      votes_votesWithLog_correspond {| nwPackets := ps'; nwState := st' |}.
  Proof.
    red. unfold votes_votesWithLog_correspond. split; intros; break_and.
    - unfold votes_votesWithLog in *; intros.
      repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
      simpl in *. break_or_hyp; repeat break_exists; break_and.
      + repeat find_rewrite. eauto.
      + repeat find_rewrite. simpl in *. intuition; try tuple_inversion; eauto.
    - unfold votesWithLog_votes in *; intros.
      repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
      simpl in *. break_or_hyp; repeat break_exists; break_and.
      + repeat find_rewrite. eauto.
      + repeat find_rewrite. simpl in *. intuition.
        * eexists. tuple_inversion. intuition.
        * find_apply_hyp_hyp. break_exists. eexists. eauto.
  Qed.

  Ltac start :=
    red; intros; eapply votes_votesWithLog_correspond_cases; eauto.

  Ltac finish :=
    repeat break_match; subst_max; first [
      left; solve[eauto] |
      right; repeat eexists; solve[eauto]
    ].

  Ltac unfold_all :=
    red; unfold votes_votesWithLog_correspond, votes_votesWithLog, votesWithLog_votes.

  Lemma votes_votesWithLog_correspond_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      votes_votesWithLog_correspond net.
  Proof.
    intros.
    apply refined_raft_net_invariant; auto.
    - unfold_all. simpl. split; contradiction.
    - start. unfold update_elections_data_client_request in *. finish.
    - start. unfold update_elections_data_timeout in *. finish.
    - start. unfold update_elections_data_appendEntries in *. finish.
    - start. subst; auto.
    - start. unfold update_elections_data_requestVote in *. finish.
    - start. unfold update_elections_data_requestVoteReply in *. finish.
    - start. find_rewrite. auto.
    - start. find_rewrite. auto.
    - unfold_all. split; intros; break_and;
      repeat find_reverse_higher_order_rewrite; eauto.
    - unfold_all.
      intuition; find_higher_order_rewrite;
      (update_destruct; subst; rewrite_update; [|eauto]);
      unfold reboot in *; simpl in *;
      (eapply equates_1; [
          match goal with
          | H : _ |- _ => solve [ eapply H; aggressive_rewrite_goal; eauto ]
          end |]);
      find_rewrite; auto.
  Qed.

  Instance vvci : votes_votesWithLog_correspond_interface.
  Proof.
    split. exact votes_votesWithLog_correspond_invariant.
  Defined.

End VotesVotesWithLogCorrespond.
