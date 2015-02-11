Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import VerdiTactics.
Require Import Raft.

Section OneLeaderPerTerm.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition one_leader_per_term (net : network) :=
    forall h h',
      currentTerm (nwState net h) = currentTerm (nwState net h') ->
      type (nwState net h) = Leader ->
      type (nwState net h') = Leader ->
      h = h'.

  Lemma plus_gt_0 :
    forall a b,
      a + b > 0 ->
      a > 0 \/ b > 0.
  Proof.
    intros.
    destruct (eq_nat_dec a 0); intuition.
  Qed.

  Lemma pigeon :
    forall A (A_eq_dec : forall a a': A, {a = a'} + {a <> a'}) (l : list A) sub1 sub2,
      (forall a, In a sub1 -> In a l) ->
      (forall a, In a sub2 -> In a l) ->
      NoDup l ->
      NoDup sub1 ->
      NoDup sub2 ->
      length sub1 + length sub2 > length l ->
      exists a, In a sub1 /\ In a sub2.
  Proof.
    induction l.
    intros.
    + simpl in *. find_apply_lem_hyp plus_gt_0. intuition.
      * destruct sub1; simpl in *; [omega|].
        specialize (H a). intuition.
      * destruct sub2; simpl in *; [omega|].
        specialize (H0 a). intuition.
    + intros. simpl in *.
      destruct (in_dec A_eq_dec a sub1);
        destruct (in_dec A_eq_dec a sub2); eauto;
            specialize (IHl (remove A_eq_dec a sub1) (remove A_eq_dec a sub2));
            cut (exists a0, In a0 (remove A_eq_dec a sub1) /\ In a0 (remove A_eq_dec a sub2));
            try solve [intros; break_exists;
                       intuition eauto using in_remove];
            apply IHl; try solve [
                             intros; find_copy_apply_lem_hyp in_remove;
                             find_apply_hyp_hyp; intuition; subst; exfalso; eapply remove_In; eauto];
            eauto using remove_NoDup; try solve_by_inversion;
            repeat match goal with
                     | H : ~ In a ?sub |- _ =>
                       assert (length (remove A_eq_dec a sub) = length sub)
                         by eauto using remove_length_not_in; clear H
                     | H : In a ?sub |- _ =>
                       assert (length (remove A_eq_dec a sub) >= length sub - 1)
                         by eauto using remove_length_ge; clear H
                   end; omega.
  Qed.

  Functional Scheme div2_ind := Induction for div2 Sort Prop.

  Theorem div2_correct' :
    forall n,
      n <= div2 n + S (div2 n).
  Proof.
    intro n. functional induction (div2 n); omega.
  Qed.

  Theorem div2_correct :
    forall c a b,
      a > div2 c ->
      b > div2 c ->
      a + b > c.
  Proof.
    intros n. functional induction (div2 n); intros; try omega.
    specialize (IHn0 (pred a) (pred b)). omega.
  Qed.

  Lemma wonElection_one_in_common :
    forall l l',
      wonElection (dedup name_eq_dec l) = true ->
      wonElection (dedup name_eq_dec l') = true ->
      exists h, In h l /\ In h l'.
  Proof.
    intros. unfold wonElection in *. do_bool.
    cut (exists h, In h (dedup name_eq_dec l) /\ In h (dedup name_eq_dec l'));
      [intros; break_exists; exists x; intuition eauto using in_dedup_was_in|].
    eapply pigeon with (l := nodes); eauto using all_fin_all, all_fin_NoDup, NoDup_dedup, name_eq_dec, div2_correct.
  Qed.

  Ltac copy_eapply_prop_hyp P H :=
    match goal with
      | H' : P _ |- _ =>
        let x := fresh in
        pose proof H as x;
          apply H' in x
    end.

  Require Import RaftRefinement.
  Require Import CroniesCorrect.
  Require Import VotesCorrect.

  Lemma one_leader_per_term_invariant' :
    forall net,
      votes_correct net ->
      cronies_correct net ->
      one_leader_per_term (deghost net).
  Proof.
    unfold votes_correct, cronies_correct, one_leader_per_term in *.
    intuition.
    repeat match goal with
             | H : context [ nwState (deghost _) _ ] |- _ =>
               rewrite deghost_spec in H
           end.
    match goal with
      | h : type _ = _, h' : type _ = _ |- _ =>
        copy_eapply_prop_hyp votes_received_leaders h;
          copy_eapply_prop_hyp votes_received_leaders h'
    end.
    match goal with
      | H : wonElection _ = _ |- _ =>
        find_eapply_lem_hyp wonElection_one_in_common; [|clear H; eauto]
    end.
    break_exists; intuition.
    eapply_prop one_vote_per_term;
      eapply_prop cronies_votes;
      [eapply_prop votes_received_cronies|];
      intuition eauto.
    unfold raft_data in *. unfold raft_refined_base_params, raft_refined_multi_params in *.
    repeat find_rewrite.
    eapply_prop votes_received_cronies; intuition eauto.
  Qed.

  Theorem one_leader_per_term_invariant :
    forall net,
      raft_intermediate_reachable net -> one_leader_per_term net.
  Proof.
    intros.
    apply lower_prop; auto.
    intros.
    apply one_leader_per_term_invariant'.
    - eauto using votes_correct_invariant.
    - eauto using cronies_correct_invariant.
  Qed.
End OneLeaderPerTerm.
