Require Import Arith.
Require Import NPeano.
Require Import Omega.
Require Import PeanoNat.
Import Nat.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Export CommonDefinitions.

Section CommonTheorems.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma uniqueIndices_elim_eq :
    forall xs x y,
      uniqueIndices xs ->
      In x xs ->
      In y xs ->
      eIndex x = eIndex y ->
      x = y.
  Proof.
    unfold uniqueIndices.
    eauto using NoDup_map_elim.
  Qed.

  Lemma sorted_cons :
    forall xs a,
      sorted xs ->
      (forall a', In a' xs -> eIndex a > eIndex a' /\ eTerm a >= eTerm a') ->
      sorted (a :: xs).
  Proof.
    intros.
    simpl in *. intuition;
      find_apply_hyp_hyp; intuition.
  Qed.

  Lemma sorted_subseq :
    forall ys xs,
      subseq xs ys ->
      sorted ys ->
      sorted xs.
  Proof.
    induction ys; intros; simpl in *.
    - break_match; intuition.
    - break_match; intuition.
      subst. apply sorted_cons; eauto.
      intros. eauto using subseq_In.
  Qed.

  Theorem maxTerm_is_max :
    forall l e,
      sorted l ->
      In e l ->
      maxTerm l >= eTerm e.
  Proof.
    induction l; intros.
    - simpl in *. intuition.
    - simpl in *. intuition.
      + subst. auto with *.
      + find_apply_hyp_hyp. omega.
  Qed.

  Theorem maxIndex_is_max :
    forall l e,
      sorted l ->
      In e l ->
      maxIndex l >= eIndex e.
  Proof.
    induction l; intros.
    - simpl in *. intuition.
    - simpl in *. intuition.
      + subst. auto with *.
      + find_apply_hyp_hyp. omega.
  Qed.

  Theorem S_maxIndex_not_in :
    forall l e,
      sorted l ->
      eIndex e = S (maxIndex l) ->
      ~ In e l.
  Proof.
    intros. intro.
    find_apply_lem_hyp maxIndex_is_max; auto.
    subst. omega.
  Qed.

  Lemma maxIndex_non_empty :
    forall l,
      l <> nil ->
      exists e,
        In e l /\ maxIndex l = eIndex e /\ maxTerm l = eTerm e.
  Proof.
    destruct l; intros; simpl in *; eauto; congruence.
  Qed.

  Lemma removeAfterIndex_subseq :
    forall l i,
      subseq (removeAfterIndex l i) l.
  Proof.
    induction l; intros; simpl; auto.
    repeat break_match; intuition.
    - find_inversion. eauto using subseq_refl.
    - right. find_reverse_rewrite. auto.
  Qed.

  Lemma removeAfterIndex_sorted :
    forall l i,
      sorted l ->
      sorted (removeAfterIndex l i).
  Proof.
    intros. eauto using removeAfterIndex_subseq, sorted_subseq.
  Qed.

  Lemma removeAfterIndex_in :
    forall l i a,
      In a (removeAfterIndex l i) ->
      In a l.
  Proof.
    eauto using removeAfterIndex_subseq, subseq_In.
  Qed.


  Lemma findAtIndex_not_in :
    forall l e,
      sorted l ->
      findAtIndex l (eIndex e) = None ->
      ~ In e l.
  Proof.
    induction l; intros; intro.
    - intuition.
    - simpl in *. break_match; try discriminate. intuition.
      + subst. rewrite <- beq_nat_refl in *. discriminate.
      + find_copy_apply_hyp_hyp. intuition. break_if; do_bool; eauto. omega.
  Qed.

  Lemma findAtIndex_in :
    forall l i e',
      findAtIndex l i = Some e' ->
      In e' l.
  Proof.
    induction l; intros.
    - discriminate.
    - simpl in *. break_match.
      + find_inversion. auto.
      + break_if; eauto; discriminate.
  Qed.

  Lemma findAtIndex_index :
    forall l i e',
      findAtIndex l i = Some e' ->
      i = eIndex e'.
  Proof.
    induction l; intros.
    - discriminate.
    - simpl in *. break_match.
      + find_inversion. apply beq_nat_true in Heqb. auto.
      + break_if; eauto; discriminate.
  Qed.

  Lemma NoDup_removeAfterIndex :
    forall l i,
      NoDup l ->
      NoDup (removeAfterIndex l i).
  Proof.
    eauto using subseq_NoDup, removeAfterIndex_subseq.
  Qed.

  Notation disjoint xs ys := (forall x, In x xs -> In x ys -> False).

  Lemma removeAfterIndex_le_In :
    forall xs i x,
      eIndex x <= i ->
      In x xs ->
      In x (removeAfterIndex xs i).
  Proof.
    induction xs; intros.
    - intuition.
    - simpl in *. break_if; simpl in *; intuition.
      subst. do_bool. omega.
  Qed.

  Lemma removeAfterIndex_In_le :
    forall xs i x,
      sorted xs ->
      In x (removeAfterIndex xs i) ->
      eIndex x <= i.
  Proof.
    induction xs; intros.
    - simpl in *. intuition.
    - simpl in *.
      break_if; simpl in *; do_bool; intuition; subst; auto.
      find_apply_hyp_hyp. omega.
  Qed.

  Lemma removeAfterIndex_covariant :
    forall xs ys i x,
      sorted xs ->
      sorted ys ->
      In x (removeAfterIndex xs i) ->
      (forall x, In x xs -> In x ys) ->
      In x (removeAfterIndex ys i).
  Proof.
    induction xs; intros.
    - simpl in *. intuition.
    - simpl in *.
      break_match; simpl in *; intuition;
      subst; do_bool;
      match goal with
        | e : entry, H : forall _, _ = _ \/ _ -> _ |- _ =>
          specialize (H e)
      end;
      intuition.
      + eauto using removeAfterIndex_le_In.
      + find_apply_hyp_hyp. intuition.
        match goal with
          | _ : eIndex ?e <= ?li, _ : eIndex ?e > eIndex ?e' |- _ =>
            assert (eIndex e' <= li) by omega
        end.
        eauto using removeAfterIndex_le_In.
  Qed.

  Lemma removeAfterIndex_le :
    forall xs i j,
      i <= j ->
      removeAfterIndex xs i = removeAfterIndex (removeAfterIndex xs j) i.
  Proof.
    induction xs; intros.
    - reflexivity.
    - simpl.
      find_copy_apply_hyp_hyp.
      repeat (break_if; simpl in *; intuition); try discriminate.
      do_bool. omega.
  Qed.

  Lemma removeAfterIndex_2_subseq :
    forall xs i j,
      subseq (removeAfterIndex (removeAfterIndex xs i) j) (removeAfterIndex (removeAfterIndex xs j) i).
  Proof.
    induction xs; intros; simpl.
    - auto.
    - repeat (break_match; simpl); intuition; try discriminate.
      + eauto using subseq_refl.
      + do_bool. assert (j < i) by omega.
        rewrite removeAfterIndex_le with (j := i) (i := j) at 1; auto; omega.
      + do_bool. assert (i < j) by omega.
        rewrite removeAfterIndex_le with (i := i) (j := j) at 2; auto; omega.
  Qed.

  Lemma removeAfterIndex_comm :
    forall xs i j,
      removeAfterIndex (removeAfterIndex xs i) j =
      removeAfterIndex (removeAfterIndex xs j) i.
  Proof.
    auto using subseq_subseq_eq, removeAfterIndex_2_subseq.
  Qed.

  Lemma removeAfterIndex_2_eq_min :
    forall xs i j,
      removeAfterIndex (removeAfterIndex xs i) j =
      removeAfterIndex xs (min i j).
  Proof.
    intros.
    pose proof Min.min_spec i j. intuition.
    - find_rewrite. rewrite removeAfterIndex_le with (i := i) (j := j) at 2;
        eauto using removeAfterIndex_comm; omega.
    - find_rewrite.
      rewrite <- removeAfterIndex_le with (i := j) (j := i);
        auto; omega.
  Qed.

  Lemma findAtIndex_None :
    forall xs i x,
      sorted xs ->
      findAtIndex xs i = None ->
      In x xs ->
      eIndex x <> i.
  Proof.
    induction xs; intros; simpl in *; intuition; break_match; try discriminate.
    - subst. do_bool. congruence.
    - do_bool. break_if; eauto.
      do_bool. find_apply_hyp_hyp. intuition.
  Qed.

  Lemma findAtIndex_removeAfterIndex_agree :
    forall xs i j e e',
      NoDup (map eIndex xs) ->
      findAtIndex xs i = Some e ->
      findAtIndex (removeAfterIndex xs j) i = Some e' ->
      e = e'.
  Proof.
    intros.
    eapply NoDup_map_elim with (f := eIndex); eauto using findAtIndex_in, removeAfterIndex_in.
    apply findAtIndex_index in H0.
    apply findAtIndex_index in H1.
    congruence.
  Qed.

  Lemma subseq_uniqueIndices :
    forall ys xs,
      subseq xs ys ->
      uniqueIndices ys ->
      uniqueIndices xs.
  Proof.
    unfold uniqueIndices.
    induction ys; intros.
    - simpl in *. break_match; intuition.
    - simpl in *. break_match; intuition.
      + simpl. constructor.
      + subst. simpl in *. invc H0. constructor; auto.
        intro. apply H3.
        eapply subseq_In; eauto.
        apply subseq_map. auto.
      + subst. invc H0. eauto.
  Qed.

  Lemma subseq_findGtIndex :
    forall xs i,
      subseq (findGtIndex xs i) xs.
  Proof.
    induction xs; intros.
    - simpl. auto.
    - simpl. repeat break_match; auto.
      + find_inversion. eauto.
      + congruence.
  Qed.

  Lemma findGtIndex_in :
    forall xs i x,
      In x (findGtIndex xs i) ->
      In x xs.
  Proof.
    eauto using subseq_In, subseq_findGtIndex.
  Qed.

  Lemma findGtIndex_sufficient :
    forall e entries x,
      sorted entries ->
      In e entries ->
      eIndex e > x ->
      In e (findGtIndex entries x).
  Proof.
    induction entries; intros.
    - simpl in *. intuition.
    - simpl in *. break_if; intuition.
      + subst. in_crush.
      + subst. do_bool. omega.
      + do_bool. find_apply_hyp_hyp. omega.
  Qed.

  Definition contiguous_range_exact_lo xs lo :=
    (forall i,
       lo < i <= maxIndex xs ->
       exists e,
         eIndex e = i /\
         In e xs) /\
    (forall e,
       In e xs ->
       lo < eIndex e).

  Lemma removeAfterIndex_uniqueIndices :
    forall l i,
      uniqueIndices l ->
      uniqueIndices (removeAfterIndex l i).
  Proof with eauto using subseq_uniqueIndices, removeAfterIndex_subseq.
    intros...
  Qed.

  Lemma maxIndex_subset :
    forall xs ys,
      sorted xs -> sorted ys ->
      (forall x, In x xs -> In x ys) ->
      maxIndex xs <= maxIndex (orig_base_params:=orig_base_params) ys.
  Proof.
    destruct xs; intros.
    - simpl. omega.
    - destruct ys; simpl in *.
      + match goal with
          | [ H : forall _, _ = _ \/ _ -> _, a : entry |- _ ] =>
            solve [ specialize (H a); intuition ]
        end.
    + match goal with
        | [ H : forall _, _ = _ \/ _ -> _ |- eIndex ?a <= _ ] =>
          specialize (H a); intuition
      end; subst; auto.
      find_apply_hyp_hyp. omega.
  Qed.

  Lemma maxIndex_exists_in :
    forall xs,
      maxIndex xs >= 1 ->
      exists x,
        eIndex x = maxIndex xs /\
        In x xs.
  Proof.
    destruct xs; intros.
    - simpl in *. omega.
    - simpl in *. eauto.
  Qed.

  Lemma maxIndex_app :
    forall l l',
      maxIndex (l ++ l') = maxIndex l \/
      maxIndex (l ++ l') = maxIndex l' /\ l = [].
  Proof.
    induction l; intuition.
  Qed.

  Lemma maxIndex_removeAfterIndex_le :
    forall l i,
      sorted l ->
      maxIndex (removeAfterIndex l i) <= maxIndex l.
  Proof.
    intros.
    apply maxIndex_subset; eauto using removeAfterIndex_sorted.
    intros. eauto using removeAfterIndex_in.
  Qed.

  Lemma maxIndex_removeAfterIndex :
    forall l i e,
      sorted l ->
      In e l ->
      eIndex e = i ->
      maxIndex (removeAfterIndex l i) = i.
  Proof.
    induction l; intros; simpl in *; intuition.
    - subst. break_if; do_bool; try omega.
      reflexivity.
    - break_if; simpl in *.
      + do_bool.
        match goal with
          | H : forall _, In _ _ -> _ |- _ =>
            specialize (H2 e)
        end. intuition. omega.
      + eauto.
  Qed.

  Lemma removeIncorrect_new_contiguous :
    forall new current prev e,
      sorted current ->
      uniqueIndices current ->
      (forall e e',
         eIndex e = eIndex e' ->
         eTerm e = eTerm e' ->
         In e new ->
         In e' current ->
         e = e') ->
      contiguous_range_exact_lo current 0 ->
      contiguous_range_exact_lo new prev ->
      In e current ->
      eIndex e = prev ->
      contiguous_range_exact_lo (new ++ removeAfterIndex current prev)
                                0.
  Proof.
    intros new current prev e Hsorted Huniq Hinv. intros. red. intros.
    intuition.
    - destruct (le_lt_dec i prev).
      + unfold contiguous_range_exact_lo in *. intuition.
        match goal with
          | H: forall _, _ < _ <= _ current -> _, H' : In _ current |- _ =>
            specialize (H i); apply maxIndex_is_max in H'; auto; forward H; intuition
        end.
        break_exists. exists x. intuition.
        apply in_or_app. right. subst.
        eapply removeAfterIndex_le_In; eauto.
      + pose proof maxIndex_app new (removeAfterIndex current prev). intuition.
        * find_rewrite.
          unfold contiguous_range_exact_lo in *. intuition.
          match goal with
            | H: forall _, _ < _ <= _ new -> _ |- _ =>
              specialize (H i); auto; forward H; intuition
          end. break_exists. exists x. intuition.
        * subst. simpl in *. clean.
          exfalso.
          pose proof maxIndex_removeAfterIndex current (eIndex e) e.
          intuition.
    - unfold contiguous_range_exact_lo in *.
      do_in_app. intuition.
      + firstorder.
      + firstorder using removeAfterIndex_in.
  Qed.

  Lemma incoming_entries_in_log :
    forall es log x i,
      In x es ->
      uniqueIndices log ->
      exists y,
        eIndex x = eIndex y /\
        eTerm x = eTerm y /\
        In y (es ++ (removeAfterIndex log i)).
  Proof.
    intros.
    exists x. intuition.
  Qed.

  Lemma findGtIndex_necessary :
    forall entries e x,
      In e (findGtIndex entries x) ->
      In e entries /\
      eIndex e > x.
  Proof.
    induction entries; intros; simpl in *; intuition.
    - break_if; simpl in *; intuition; right; eapply IHentries; eauto.
    - break_if;
      simpl in *; intuition.
      + do_bool. subst. omega.
      + simpl in *; intuition; eapply IHentries; eauto.
  Qed.

  Lemma findGtIndex_contiguous :
    forall entries x,
      sorted entries ->
      (forall i, 0 < i <= maxIndex entries -> (exists e, In e entries /\ eIndex e = i)) ->
      forall i, x < i <= maxIndex entries ->
           exists e, In e (findGtIndex entries x) /\ eIndex e = i.
  Proof.
    intros entries x Hsorted; intros. specialize (H i).
    conclude H ltac:(omega).
    break_exists. exists x0. intuition.
    apply findGtIndex_sufficient; auto; omega.
  Qed.

  Lemma findGtIndex_max :
    forall entries x,
      maxIndex (findGtIndex entries x) <= maxIndex entries.
  Proof.
    intros. destruct entries; simpl; auto.
    break_if; simpl; intuition.
  Qed.

  Lemma findAtIndex_uniq_equal :
    forall e e' es,
      findAtIndex es (eIndex e) = Some e' ->
      In e es ->
      uniqueIndices es ->
      e = e'.
  Proof.
    intros.
    pose proof findAtIndex_in _ _ _ H.
    pose proof findAtIndex_index _ _ _ H.
    eapply uniqueIndices_elim_eq; eauto.
  Qed.

  Definition entries_match' entries entries' :=
    forall e e' e'',
      eIndex e = eIndex e' ->
      eTerm e = eTerm e' ->
      In e entries ->
      In e' entries' ->
      eIndex e'' <= eIndex e ->
      (In e'' entries -> In e'' entries').

  Lemma entries_match_entries_match' :
    forall xs ys,
      entries_match xs ys ->
      entries_match' xs ys /\
      entries_match' ys xs.
  Proof.
    unfold entries_match, entries_match'.
    intros. intuition.
    - eapply H; eauto.
    - eapply (H e' e); eauto with *.
  Qed.

  Definition contiguous
             (prevLogIndex : logIndex)
             (prevLogTerm : term)
             (leaderLog entries : list entry) : Prop :=
    (prevLogIndex = 0 \/
     exists e, findAtIndex leaderLog prevLogIndex = Some e /\
          eTerm e = prevLogTerm) /\
    (forall e,
       In e leaderLog ->
       eIndex e > prevLogIndex ->
       eIndex e <= maxIndex entries ->
       In e entries) /\
    forall e e',
      eIndex e = eIndex e' ->
      eTerm e = eTerm e' ->
      In e entries ->
      In e' leaderLog ->
      e = e'.

  Lemma entries_match_refl :
    forall l,
      entries_match l l.
  Proof.
    unfold entries_match. intuition.
  Qed.

  Lemma entries_match_sym :
    forall xs ys,
      entries_match xs ys ->
      entries_match ys xs.
  Proof.
    intros.
    unfold entries_match in *.
    intros. intuition.
    - apply H with (e:=e')(e':=e); auto.
      repeat find_rewrite. auto.
    - apply H with (e:=e')(e':=e); auto.
      repeat find_rewrite. auto.
  Qed.

  Lemma advanceCurrentTerm_same_log :
    forall st t,
      log (advanceCurrentTerm st t) = log st.
  Proof.
    unfold advanceCurrentTerm. intros.
    break_if; auto.
  Qed.

  Lemma tryToBecomeLeader_same_log :
    forall n st out st' ms,
      tryToBecomeLeader n st = (out, st', ms) ->
      log st' = log st.
  Proof.
    unfold tryToBecomeLeader.
    intros. find_inversion. auto.
  Qed.

  Lemma handleRequestVote_same_log :
    forall n st t c li lt st' ms,
      handleRequestVote n st t c li lt = (st', ms) ->
      log st' = log st.
  Proof.
    unfold handleRequestVote.
    intros.
    repeat (break_match; try discriminate; repeat (find_inversion; simpl in *));
      auto using advanceCurrentTerm_same_log.
  Qed.

  Lemma handleRequestVoteReply_same_log :
    forall n st src t v,
      log (handleRequestVoteReply n st src t v) = log st.
  Proof.
    unfold handleRequestVoteReply.
    intros. repeat break_match; simpl; auto using advanceCurrentTerm_same_log.
  Qed.


  Lemma advanceCurrentTerm_same_lastApplied :
    forall st t,
      lastApplied (advanceCurrentTerm st t) = lastApplied st.
  Proof.
    unfold advanceCurrentTerm. intros.
    break_if; auto.
  Qed.

  Lemma tryToBecomeLeader_same_lastApplied :
    forall n st out st' ms,
      tryToBecomeLeader n st = (out, st', ms) ->
      lastApplied st' = lastApplied st.
  Proof.
    unfold tryToBecomeLeader.
    intros. find_inversion. auto.
  Qed.

  Lemma handleRequestVote_same_lastApplied :
    forall n st t c li lt st' ms,
      handleRequestVote n st t c li lt = (st', ms) ->
      lastApplied st' = lastApplied st.
  Proof.
    unfold handleRequestVote.
    intros.
    repeat (break_match; try discriminate; repeat (find_inversion; simpl in *));
      auto using advanceCurrentTerm_same_lastApplied.
  Qed.

  Lemma handleRequestVoteReply_same_lastApplied :
    forall n st src t v,
      lastApplied (handleRequestVoteReply n st src t v) = lastApplied st.
  Proof.
    unfold handleRequestVoteReply.
    intros. repeat break_match; simpl; auto using advanceCurrentTerm_same_lastApplied.
  Qed.

  Lemma findAtIndex_elim :
    forall l i e,
      findAtIndex l i = Some e ->
      i = eIndex e /\ In e l.
  Proof.
    eauto using findAtIndex_in, findAtIndex_index.
  Qed.

  Lemma index_in_bounds :
    forall e es i,
      sorted es ->
      In e es ->
      i <> 0 ->
      i <= eIndex e ->
      1 <= i <= maxIndex es.
  Proof.
    intros. split.
    - omega.
    - etransitivity; eauto. apply maxIndex_is_max; auto.
  Qed.

  Lemma rachet :
    forall x x' xs ys,
      eIndex x = eIndex x' ->
      In x xs ->
      In x' ys ->
      In x' xs ->
      uniqueIndices xs ->
      In x ys.
  Proof.
    intros.
    assert (x = x').
    - eapply uniqueIndices_elim_eq; eauto.
    - subst. auto.
  Qed.

  Lemma findAtIndex_intro :
    forall l i e,
      sorted l ->
      In e l ->
      eIndex e = i ->
      uniqueIndices l ->
      findAtIndex l i = Some e.
  Proof.
    induction l; intros.
    - simpl in *. intuition.
    - simpl in *. intuition; break_if; subst; do_bool.
      + auto.
      + congruence.
      + f_equal. eauto using uniqueIndices_elim_eq with *.
      + break_if; eauto.
        * do_bool. find_apply_hyp_hyp. omega.
        * eapply IHl; auto. unfold uniqueIndices in *.
          simpl in *. solve_by_inversion.
  Qed.

  Lemma doLeader_same_log :
    forall st n os st' ms,
      doLeader st n = (os, st', ms) ->
      log st' = log st.
  Proof.
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; auto.
  Qed.

  Lemma handleAppendEntriesReply_same_log :
    forall n st src t es b st' l,
      handleAppendEntriesReply n st src t es b = (st', l) ->
      log st' = log st.
  Proof.
    intros.
    unfold handleAppendEntriesReply in *.
    repeat (break_match; repeat (find_inversion; simpl in *)); auto using advanceCurrentTerm_same_log.
  Qed.

  Lemma handleAppendEntriesReply_same_lastApplied :
    forall n st src t es b st' l,
      handleAppendEntriesReply n st src t es b = (st', l) ->
      lastApplied st' = lastApplied st.
  Proof.
    intros.
    unfold handleAppendEntriesReply in *.
    repeat (break_match; repeat (find_inversion; simpl in *)); auto using advanceCurrentTerm_same_lastApplied.
  Qed.

  Lemma handleAppendEntries_same_lastApplied :
    forall h st t n pli plt es ci st' ps,
      handleAppendEntries h st t n pli plt es ci = (st', ps) ->
      lastApplied st' = lastApplied st.
  Proof.
    intros.
    unfold handleAppendEntries in *.
    repeat (break_match; repeat (find_inversion; simpl in *)); auto using advanceCurrentTerm_same_lastApplied.
  Qed.

  Definition term_of msg :=
    match msg with
      | RequestVote t _ _ _ => Some t
      | RequestVoteReply t _ => Some t
      | AppendEntries t _ _ _ _ _ => Some t
      | AppendEntriesReply t _ _ => Some t
    end.

  Theorem sorted_uniqueIndices :
    forall l,
      sorted l -> uniqueIndices l.
  Proof.
    intros; induction l; simpl; auto.
    - unfold uniqueIndices. simpl. constructor.
    - unfold uniqueIndices in *. simpl in *. intuition. constructor; eauto.
      intuition. do_in_map. find_apply_hyp_hyp. omega.
  Qed.


  Lemma wonElection_length :
    forall l1 l2,
      wonElection l1 = true ->
      length l1 <= length l2 ->
      wonElection l2 = true.
  Proof.
    intros.
    unfold wonElection in *. do_bool.
    omega.
  Qed.

  Lemma wonElection_no_dup_in :
    forall l1 l2,
      wonElection l1 = true ->
      NoDup l1 ->
      (forall x, In x l1 -> In x l2) ->
      wonElection l2 = true.
  Proof.
    intros.
    find_eapply_lem_hyp subset_length;
      eauto using name_eq_dec, wonElection_length.
  Qed.

  Lemma wonElection_exists_voter :
    forall l,
      wonElection l = true ->
      exists x,
        In x l.
  Proof.
    unfold wonElection.
    intros.
    destruct l; try discriminate.
    simpl. eauto.
  Qed.


  Lemma argmax_fun_ext :
    forall A (f : A -> nat) g l,
      (forall a, f a = g a) ->
      argmax f l = argmax g l.
  Proof.
    intros. induction l; simpl in *; intuition.
    find_rewrite. break_match; intuition.
    repeat find_higher_order_rewrite. auto.
  Qed.

  Lemma argmax_None :
    forall A (f : A -> nat) l,
      argmax f l = None ->
      l = [].
  Proof.
    intros. destruct l; simpl in *; intuition.
    repeat break_match; congruence.
  Qed.

  Lemma argmax_elim :
    forall A (f : A -> nat) l a,
      argmax f l = Some a ->
      (In a l /\
       forall x, In x l -> f a >= f x).
  Proof.
    induction l; intros; simpl in *; [congruence|].
    repeat break_match; find_inversion.
    - do_bool.
      match goal with
        | H : forall _, Some ?a = Some _ -> _ |- _ =>
          specialize (H a)
      end. intuition; subst; auto.
      find_apply_hyp_hyp. omega.
    - do_bool.
      match goal with
        | H : forall _, Some ?a = Some _ -> _ |- _ =>
          specialize (H a)
      end. intuition; subst; auto.
      find_apply_hyp_hyp. omega.
    - intuition; subst; auto.
      find_apply_lem_hyp argmax_None.
      subst. solve_by_inversion.
  Qed.

  Lemma argmax_in :
    forall A (f : A -> nat) l a,
      argmax f l = Some a ->
      In a l.
  Proof.
    intros. find_apply_lem_hyp argmax_elim. intuition.
  Qed.

  Lemma argmax_one_different :
    forall A (A_eq_dec : forall x y : A, {x = y} + {x <> y}) f g (l : list A) a,
      (forall x, In x l -> a <> x -> f x = g x) ->
      (forall x, In x l -> f x <= g x) ->
      (argmax g l = argmax f l \/
       argmax g l = Some a).
  Proof.
    intros. induction l; simpl in *; intuition.
    conclude IHl intuition.
    conclude IHl intuition. intuition.
    - find_rewrite. break_match; intuition.
      repeat break_if; intuition.
      + do_bool. right.
        find_apply_lem_hyp argmax_in; intuition.
        destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition;
        specialize (H0 a1); specialize (H a0); intuition; repeat find_rewrite; omega.
      + do_bool. right.
        find_apply_lem_hyp argmax_in; intuition.
        destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition.
        * specialize (H a1); specialize (H0 a0); intuition. repeat find_rewrite. omega.
        * specialize (H a1); specialize (H0 a0); intuition. repeat find_rewrite. omega.
    - find_rewrite. repeat break_match; subst; intuition.
      do_bool.
      repeat find_apply_lem_hyp argmax_elim; intuition.
      destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition.
      + specialize (H a0); specialize (H0 a1); intuition. repeat find_rewrite. omega.
      + pose proof H a0; pose proof H a1; intuition. repeat find_rewrite.
        specialize (H3 a1). intuition. omega.
  Qed.

  Lemma argmin_fun_ext :
    forall A (f : A -> nat) g l,
      (forall a, f a = g a) ->
      argmin f l = argmin g l.
  Proof.
    intros. induction l; simpl in *; intuition.
    find_rewrite. break_match; intuition.
    repeat find_higher_order_rewrite. auto.
  Qed.

  Lemma argmin_None :
    forall A (f : A -> nat) l,
      argmin f l = None ->
      l = [].
  Proof.
    intros. destruct l; simpl in *; intuition.
    repeat break_match; congruence.
  Qed.

  Lemma argmin_elim :
    forall A (f : A -> nat) l a,
      argmin f l = Some a ->
      (In a l /\
       forall x, In x l -> f a <= f x).
  Proof.
    induction l; intros; simpl in *; [congruence|].
    repeat break_match; find_inversion.
    - do_bool.
      match goal with
        | H : forall _, Some ?a = Some _ -> _ |- _ =>
          specialize (H a)
      end. intuition; subst; auto.
      find_apply_hyp_hyp. omega.
    - do_bool.
      match goal with
        | H : forall _, Some ?a = Some _ -> _ |- _ =>
          specialize (H a)
      end. intuition; subst; auto.
      find_apply_hyp_hyp. omega.
    - intuition; subst; auto.
      find_apply_lem_hyp argmin_None.
      subst. solve_by_inversion.
  Qed.

  Lemma argmin_in :
    forall A (f : A -> nat) l a,
      argmin f l = Some a ->
      In a l.
  Proof.
    intros. find_apply_lem_hyp argmin_elim. intuition.
  Qed.

  Lemma argmin_one_different :
    forall A (A_eq_dec : forall x y : A, {x = y} + {x <> y}) f g (l : list A) a,
      (forall x, In x l -> a <> x -> f x = g x) ->
      (forall x, In x l -> g x <= f x) ->
      (argmin g l = argmin f l \/
       argmin g l = Some a).
  Proof.
    intros. induction l; simpl in *; intuition.
    conclude IHl intuition.
    conclude IHl intuition. intuition.
    - find_rewrite. break_match; intuition.
      repeat break_if; intuition.
      + do_bool. right.
        find_apply_lem_hyp argmin_in; intuition.
        destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition;
        specialize (H0 a1); specialize (H a0); intuition; repeat find_rewrite; omega.
      + do_bool. right.
        find_apply_lem_hyp argmin_in; intuition.
        destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition.
        * specialize (H a1); specialize (H0 a0); intuition. repeat find_rewrite. omega.
        * specialize (H a1); specialize (H0 a0); intuition. repeat find_rewrite. omega.
    - find_rewrite. repeat break_match; subst; intuition.
      do_bool.
      repeat find_apply_lem_hyp argmin_elim; intuition.
      destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition.
      + specialize (H a0); specialize (H0 a1); intuition. repeat find_rewrite. omega.
      + pose proof H a0; pose proof H a1; intuition. repeat find_rewrite.
        specialize (H3 a1). intuition. omega.
  Qed.

  Ltac update_destruct :=
    match goal with
    | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Ltac update_destruct_hyp :=
    match goal with
    | [ _ : context [ update _ ?y _ ?x ] |- _ ] => destruct (name_eq_dec y x)
    end.


  Lemma applied_entries_update :
    forall sigma h st,
      lastApplied st >= lastApplied (sigma h) ->
      (applied_entries (update sigma h st) = applied_entries sigma /\
       (exists h',
          argmax (fun h => lastApplied (sigma h)) (all_fin N) = Some h' /\
          lastApplied (sigma h') >= lastApplied st))
      \/
      (argmax (fun h' => lastApplied (update sigma h st h')) (all_fin N) = Some h /\
       applied_entries (update sigma h st) = (rev (removeAfterIndex (log st) (lastApplied st)))).
  Proof.
    intros.
    unfold applied_entries in *.
    repeat break_match; intuition;
    try solve [find_apply_lem_hyp argmax_None;
                exfalso;
                pose proof (all_fin_all _ h); find_rewrite; intuition].
    match goal with
      | _ : argmax ?f ?l = _, _ : argmax ?g ?l = _ |- _ =>
        pose proof argmax_one_different name name_eq_dec g f l h as Hproof
    end.
    forward Hproof; [intros; rewrite_update; intuition|]; concludes.
    forward Hproof; [intros; update_destruct; subst; rewrite_update; intuition|]; concludes.
    intuition.
    - repeat find_rewrite. find_inversion.
      update_destruct; subst; rewrite_update; intuition. left.
      intuition. eexists; intuition eauto. repeat find_apply_lem_hyp argmax_elim; intuition eauto.
      match goal with
          H : _ |- _ =>
          solve [specialize (H h); rewrite_update; eauto using all_fin_all]
      end.
    - repeat find_rewrite. find_inversion. rewrite_update. intuition.
  Qed.

  Lemma applied_entries_safe_update :
    forall sigma h st,
      lastApplied st = lastApplied (sigma h) ->
      removeAfterIndex (log st) (lastApplied (sigma h))
      = removeAfterIndex (log (sigma h)) (lastApplied (sigma h)) ->
      applied_entries (update sigma h st) = applied_entries sigma.
  Proof.
    intros. unfold applied_entries in *.
    repeat break_match; repeat find_rewrite; intuition;
    match goal with
      | _ : argmax ?f ?l = _, _ : argmax ?g ?l = _ |- _ =>
        assert (argmax f l = argmax g l) by
            (apply argmax_fun_ext; intros; update_destruct; subst; rewrite_update; auto)
    end; repeat find_rewrite; try congruence.
    match goal with | H : Some _ = Some _ |- _ => inversion H end.
    subst. clean.
    f_equal. update_destruct; subst; rewrite_update; repeat find_rewrite; auto.
  Qed.


  Lemma applied_entries_log_lastApplied_same :
    forall sigma sigma',
      (forall h, log (sigma' h) = log (sigma h)) ->
      (forall h, lastApplied (sigma' h) = lastApplied (sigma h)) ->
      applied_entries sigma' = applied_entries sigma.
  Proof.
    intros.
    unfold applied_entries in *.
    rewrite argmax_fun_ext with (g := fun h : name => lastApplied (sigma h)); intuition.
    break_match; auto.
    repeat find_higher_order_rewrite. auto.
  Qed.

  Lemma applied_entries_log_lastApplied_update_same :
    forall sigma h st,
      log st = log (sigma h) ->
      lastApplied st = lastApplied (sigma h) ->
      applied_entries (update sigma h st) = applied_entries sigma.
  Proof.
    intros.
    apply applied_entries_log_lastApplied_same;
      intros; update_destruct; subst; rewrite_update; auto.
  Qed.

  Lemma applied_entries_cases :
    forall sigma,
      applied_entries sigma = [] \/
      exists h,
        applied_entries sigma = rev (removeAfterIndex (log (sigma h)) (lastApplied (sigma h))).
  Proof.
    intros.
    unfold applied_entries in *.
    break_match; simpl in *; intuition eauto.
  Qed.

  Lemma removeAfterIndex_partition :
    forall l x,
      exists l',
        l = l' ++ removeAfterIndex l x.
  Proof.
    intros; induction l; simpl in *; intuition eauto using app_nil_r.
    break_exists. break_if; [exists nil; eauto|].
    do_bool.
    match goal with
      | l : list entry, e : entry |- _ =>
        solve [exists (e :: l); simpl in *; f_equal; auto]
    end.
  Qed.

  Lemma entries_match_scratch :
    forall es ys plt,
      sorted es ->
      uniqueIndices ys ->
      (forall e1 e2,
         eIndex e1 = eIndex e2 ->
         eTerm e1 = eTerm e2 ->
         In e1 es ->
         In e2 ys ->
         (forall e3,
            eIndex e3 <= eIndex e1 ->
            In e3 es ->
            In e3 ys) /\
         (0 <> 0 ->
          exists e4,
            eIndex e4 = 0 /\
            eTerm e4 = plt /\
            In e4 ys)) ->
      (forall i, 0 < i <= maxIndex es -> exists e, eIndex e = i /\ In e es) ->
      (forall e,
         In e es ->
         0 < eIndex e) ->
      (forall y, In y ys -> 0 < eIndex y) ->
      entries_match es ys.
  Proof.
    intros.
    unfold entries_match. intuition.
    - match goal with
        | [ H : _ |- _ ] => solve [eapply H; eauto]
      end.
    - match goal with
        | [ H : forall _ _, _, H' : eIndex ?e1 = eIndex ?e2 |- _ ] =>
          specialize (H e1 e2); do 4 concludes
      end. intuition.
        match goal with
          | [ H : forall _, _ < _ <= _ -> _,
              _ : eIndex ?e3 <= eIndex _
                |- _ ] =>
            specialize (H (eIndex e3));
              conclude H
                       ltac:(split; [eauto|
                                     eapply le_trans; eauto; apply maxIndex_is_max; eauto])

        end.
        break_exists. intuition.
        match goal with
          | [ _ : In ?x _,
              _ : eIndex ?x = eIndex ?e3,
              _ : eIndex ?e3 <= eIndex _ |- _ ] =>
            eapply rachet with (x' := x); eauto using sorted_uniqueIndices
        end.
        match goal with
          | [ H : _ |- _ ] => solve [ eapply H; eauto; congruence ]
        end.
  Qed.

  Ltac use_entries_match :=
    match goal with
      | [ _ : eIndex ?e1 = eIndex ?e2,
              H : context [entries_match]
                              |- _ ] =>
        first [ solve [eapply H with (e:=e2)(e':=e1); eauto; congruence] |
                solve [eapply H with (e:=e1)(e':=e2); eauto; congruence]]
    end.

  Lemma entries_match_append :
    forall xs ys es ple pli plt,
      sorted xs ->
      sorted ys ->
      sorted es ->
      entries_match xs ys ->
      (forall e1 e2,
         eIndex e1 = eIndex e2 ->
         eTerm e1 = eTerm e2 ->
         In e1 es ->
         In e2 ys ->
         (forall e3,
            eIndex e3 <= eIndex e1 ->
            In e3 es ->
            In e3 ys) /\
         (pli <> 0 ->
          exists e4,
            eIndex e4 = pli /\
            eTerm e4 = plt /\
            In e4 ys)) ->
      (forall i, pli < i <= maxIndex es -> exists e, eIndex e = i /\ In e es) ->
      (forall e,
         In e es ->
         pli < eIndex e) ->
      findAtIndex xs pli = Some ple ->
      eTerm ple = plt ->
      pli <> 0 ->
      entries_match (es ++ removeAfterIndex xs pli) ys.
  Proof.
    intros.
    unfold entries_match. intros. split; intros.
    - in_crush_start.
      + match goal with
          | [ H : _ |- _ ] => solve [eapply H; eauto]
        end.
      + exfalso.
        find_apply_lem_hyp removeAfterIndex_In_le; intuition.
        find_apply_hyp_hyp. omega.
      + find_apply_lem_hyp findAtIndex_elim.
        intuition subst.
        match goal with
          | [ H : forall _ _, _, H' : eIndex ?e1 = eIndex ?e2 |- _ ] =>
            specialize (H e1 e2); do 4 concludes
        end.
        intuition. break_exists.
        intuition.
        find_copy_apply_lem_hyp removeAfterIndex_In_le; intuition.
        find_apply_lem_hyp removeAfterIndex_in.
        use_entries_match.
      + repeat find_apply_lem_hyp removeAfterIndex_in. use_entries_match.
    - in_crush_start.
      + match goal with
          | [ H : forall _ _, _, H' : eIndex ?e1 = eIndex ?e2 |- _ ] =>
            specialize (H e1 e2); do 4 concludes
        end.
        intuition. break_exists. intuition.
        destruct (le_lt_dec (eIndex e'') pli).
        * apply in_or_app. right.
          apply removeAfterIndex_le_In; auto.
          find_apply_lem_hyp findAtIndex_elim. intuition.
          subst. use_entries_match.
        * apply in_or_app. left.
          match goal with
            | H : forall _, _ < _ <= _ -> _ |- In ?e _ =>
              specialize (H (eIndex e))
          end.
          intuition.
          conclude_using ltac:(eapply le_trans; eauto; apply maxIndex_is_max; eauto).
          break_exists. intuition.
          match goal with
            | _: eIndex ?e1 = eIndex ?e2 |- context [ ?e2 ] =>
              eapply rachet with (x' := e1); eauto using sorted_uniqueIndices with *
          end.
      + apply in_or_app. right.
        find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
        apply removeAfterIndex_le_In; [omega|].
        find_apply_lem_hyp removeAfterIndex_in.
        use_entries_match.
  Qed.

  Lemma doLeader_appliedEntries :
  forall sigma h os st' ms,
    doLeader (sigma h) h = (os, st', ms) ->
    applied_entries (update sigma h st') = applied_entries sigma.
  Proof.
    intros.
    apply applied_entries_log_lastApplied_same.
    - intros. update_destruct; subst; rewrite_update; auto.
      eapply doLeader_same_log; eauto.
    - intros. update_destruct; subst; rewrite_update; auto.
      unfold doLeader in *. repeat break_match; find_inversion; auto.
  Qed.

  Lemma applyEntries_spec :
    forall es h st os st',
      applyEntries h st es = (os, st') ->
      exists d cc,
        st' = {[ {[ st with stateMachine := d ]} with clientCache := cc ]}.
  Proof.
    induction es; intros; simpl in *; intuition.
    - find_inversion. destruct st'; repeat eexists; eauto.
    - unfold applyEntry in *.
      repeat break_match; repeat find_inversion;
      find_apply_hyp_hyp; break_exists; repeat eexists; eauto.
  Qed.

  Lemma applyEntries_spec_ind :
    forall {es h st os st'},
      applyEntries h st es = (os, st') ->
      forall P : raft_data -> Prop,
        (forall d cc,
           P {[ {[ st with stateMachine := d ]} with clientCache := cc ]}) ->
        P st'.
  Proof.
    intros.
    find_apply_lem_hyp applyEntries_spec.
    break_exists. subst. eauto.
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

  Lemma fst_execute_log' :
    forall log st tr,
      fst (execute_log' log st tr) = tr ++ fst (execute_log' log st []).
  Proof.
    induction log; intros.
    - simpl. rewrite app_nil_r. auto.
    - simpl. break_let. rewrite IHlog. rewrite app_ass. simpl.
      rewrite IHlog with (tr := [(eInput a, o)]).
      auto.
  Qed.

  Lemma snd_execute_log' :
    forall log st tr,
      snd (execute_log' log st tr) = snd (execute_log' log st []).
  Proof.
    induction log; intros.
    - auto.
    - simpl. break_let. rewrite IHlog.
      rewrite IHlog with (tr := [(eInput a, o)]).
      auto.
  Qed.

  Lemma execute_log_correct' :
    forall log st,
      step_1_star st (snd (execute_log' log st []))
                  (fst (execute_log' log st [])).
  Proof.
    induction log; intros.
    - simpl. constructor.
    - simpl. break_let.
      rewrite fst_execute_log'.
      rewrite snd_execute_log'.
      unfold step_1_star in *.
      econstructor.
      + constructor. eauto.
      + auto.
  Qed.

  Lemma execute_log_correct :
    forall log,
      step_1_star init (snd (execute_log log))
                  (fst (execute_log log)).
  Proof.
    intros. apply execute_log_correct'.
  Qed.

  Lemma contiguous_app :
    forall l1 l2 i,
      sorted (l1 ++ l2) ->
      contiguous_range_exact_lo (l1 ++ l2) i ->
      contiguous_range_exact_lo l2 i.
  Proof.
  Admitted.

  Lemma prefix_contiguous :
    forall l l' e i,
      Prefix l' l ->
      sorted l ->
      In e l ->
      eIndex e > i ->
      contiguous_range_exact_lo l' i ->
      In e l'.
  Proof.
  Admitted.

  Lemma cons_contiguous_sorted :
    forall l i a,
      sorted (a :: l) ->
      contiguous_range_exact_lo (a :: l) i ->
      contiguous_range_exact_lo l i.
  Proof.
  Admitted.
  
  Lemma removeAfterIndex_contiguous :
    forall l i i',
      sorted l ->
      contiguous_range_exact_lo l i ->
      contiguous_range_exact_lo (removeAfterIndex l i') i.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; auto.
    do_bool.
    eapply IHl; eauto.
    eapply cons_contiguous_sorted; eauto.
    simpl; intuition.
  Qed.



  Lemma sorted_NoDup :
    forall l,
      sorted l -> NoDup l.
  Proof.
    induction l; intros; simpl in *; auto.
    - constructor.
    - constructor; intuition.
      match goal with
        | H : forall _, _ |- _ => specialize (H a)
      end. intuition.
  Qed.

  Lemma sorted_Permutation_eq :
    forall l l',
      sorted l ->
      sorted l' ->
      Permutation l l' ->
      l = l'.
  Proof.
    induction l; intros.
    - symmetry. apply Permutation_nil. assumption.
    - destruct l'.
      + apply Permutation_nil. apply Permutation_sym. assumption.
      + simpl in *. intuition.
        find_copy_eapply_lem_hyp Permutation_in; intuition.
        find_copy_apply_lem_hyp Permutation_sym.
        find_copy_eapply_lem_hyp Permutation_in; intuition.
        simpl in *. intuition;
          try (subst a; f_equal; eauto using Permutation_cons_inv).
        repeat find_apply_hyp_hyp. intuition.
        omega.
  Qed.

  Lemma removeAfterIndex_same_sufficient :
    forall x l l',
      sorted l ->
      sorted l' ->
      (forall e, eIndex e <= x ->
            In e l ->
            In e l') ->
      (forall e, eIndex e <= x ->
            In e l' ->
            In e l) ->
      removeAfterIndex l' x = removeAfterIndex l x.
  Proof.
    intros. apply sorted_Permutation_eq;
      try (apply removeAfterIndex_sorted; assumption).
    apply NoDup_Permutation;
      try (apply NoDup_removeAfterIndex; apply sorted_NoDup; assumption).
    split; intros; apply removeAfterIndex_le_In;
        eauto using removeAfterIndex_In_le, removeAfterIndex_in.
  Qed.

  Lemma removeAfterIndex_same_sufficient' :
    forall x l l',
      sorted l ->
      sorted l' ->
      contiguous_range_exact_lo l 0 ->
      (forall e, In e l' -> 0 < eIndex e) ->
      x <= maxIndex l ->
      (forall e, eIndex e <= x ->
            In e l ->
            In e l') ->
      removeAfterIndex l' x = removeAfterIndex l x.
  Proof.
    intros.
    eapply removeAfterIndex_same_sufficient; eauto.
    intros.
    unfold contiguous_range_exact_lo in *. intuition.
    specialize (H7 (eIndex e)).
    intuition. find_copy_apply_hyp_hyp.
    repeat conclude_using omega.
    break_exists. intuition.
    symmetry in H9. copy_apply H4 H10; try omega.
    eapply rachet with (xs := l'); eauto using sorted_uniqueIndices.
  Qed.

  Lemma thing2 :
    forall l l' i,
      l <> [] ->
      Prefix l l' ->
      sorted l' ->
      contiguous_range_exact_lo l i ->
      contiguous_range_exact_lo l' 0 ->
      l ++ (removeAfterIndex l' i) = l'.
  Proof.
    admit.
  Qed.

  Lemma thing :
    forall es l l' e e',
      sorted l ->
      sorted l' ->
      entries_match l l' ->
      es <> [] ->
      Prefix es l' ->
      contiguous_range_exact_lo es (eIndex e) ->
      In e l ->
      In e' l' ->
      eIndex e = eIndex e' ->
      eTerm e = eTerm e' ->
      es ++ (removeAfterIndex l (eIndex e)) = l'.
  Proof.
  Admitted.



  Lemma sorted_findGtIndex_0 :
    forall l,
      (forall e, In e l -> eIndex e > 0) ->
      sorted l ->
      findGtIndex l 0 = l.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; intuition.
    - f_equal. auto.
    - do_bool. specialize (H a); intuition; omega.
  Qed.
  
  Lemma Prefix_refl :
    forall A (l : list A),
      Prefix l l.
  Proof.
    intros. induction l; simpl in *; auto.
  Qed.

  
  Lemma findGtIndex_app_in_1 :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      In e l1 ->
      exists l',
        findGtIndex (l1 ++ l2) (eIndex e) = l' /\
        forall x,
          In x l' -> In x l1.
  Proof.
    induction l1; intros; simpl in *; intuition.
    - subst. break_if; do_bool; try omega.
      eexists; repeat (simpl in *; intuition).
    - specialize (H1 e); intuition. conclude H1 ltac:(apply in_app_iff; intuition).
      break_if; do_bool; try omega. eexists; intuition; eauto.
      simpl in *. intuition.
      eapply_prop_hyp sorted sorted; eauto. break_exists; intuition.
      find_rewrite. eauto.
  Qed.
  
  Lemma sorted_app_in_1 :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      eIndex e > 0 ->
      In e l1 ->
      eIndex e > maxIndex l2.
  Proof.
    induction l1; intros; simpl in *; intuition.
    subst. destruct l2; simpl in *; auto.
    specialize (H2 e0); concludes; intuition.
  Qed.

  Lemma findGtIndex_Prefix :
    forall l i,
      Prefix (findGtIndex l i) l.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; simpl in *; intuition.
  Qed.
  
  Lemma findGtIndex_app_in_2 :
    forall l1 l2 e,
      sorted (l1 ++ l2) ->
      In e l2 ->
      exists l',
        findGtIndex (l1 ++ l2) (eIndex e) = l1 ++ l' /\
        Prefix l' l2.
  Proof.
    induction l1; intros; simpl in *; intuition.
    - eexists; intuition eauto using findGtIndex_Prefix.
    - break_if; simpl in *; intuition.
      + eapply_prop_hyp sorted sorted; eauto.
        break_exists; intuition; find_rewrite; eauto.
      + do_bool. specialize (H1 e); conclude H1 ltac:(apply in_app_iff; intuition).
        omega.
  Qed.

  Lemma findGtIndex_nil :
    forall l i,
      (forall e', In e' l -> eIndex e' <= i) ->
      findGtIndex l i = [].
  Proof.
    intros; induction l; simpl in *; intuition.
    break_if; do_bool; intuition.
    specialize (H a); intuition. omega.
  Qed.
  
  Lemma findGtIndex_removeAfterIndex_commute :
    forall l i i',
      sorted l ->
      removeAfterIndex (findGtIndex l i) i' =
      findGtIndex (removeAfterIndex l i') i.
  Proof.
    intros. induction l; simpl in *; auto.
    repeat (break_if; simpl; intuition); do_bool;
    try congruence.
    symmetry. apply findGtIndex_nil.
    intros. find_apply_lem_hyp removeAfterIndex_in.
    find_apply_hyp_hyp. intuition.
  Qed.

  Lemma findGtIndex_app_1 :
    forall l l' i,
      maxIndex l' <= i ->
      findGtIndex (l ++ l') i = findGtIndex l i.
  Proof.
    induction l; intros; simpl in *; intuition.
    - destruct l'; simpl in *; intuition.
      break_if; do_bool; auto; omega.
    - break_if; do_bool; auto.
      f_equal. eauto.
  Qed.

  Lemma findGtIndex_app_2 :
    forall l l' i,
      sorted (l ++ l') ->
      i < maxIndex l' ->
      findGtIndex (l ++ l') i = l ++ findGtIndex l' i.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; do_bool; auto.
    - f_equal. eauto.
    - exfalso.
      destruct l'; simpl in *; intuition.
      specialize (H1 e); conclude_using intuition; intuition.
  Qed.

  Lemma thing3 :
    forall l l' e,
      sorted (l ++ l') ->
      (forall e', In e' (l ++ l') -> eIndex e' > 0) ->
      In e (l ++ l') ->
      eIndex e <= maxIndex l' ->
      In e l'.
  Proof.
    induction l; intros; simpl in *; intuition.
    subst. destruct l'; simpl in *; intuition.
    - exfalso. specialize (H0 e). intuition.
    - exfalso. specialize (H3 e0). conclude_using intuition.
      intuition.
  Qed.
  
  Lemma findGtIndex_non_empty :
    forall l i,
      i < maxIndex l ->
      findGtIndex l i <> [].
  Proof.
    intros. induction l; simpl in *; intuition.
    break_if; do_bool; simpl in *; intuition.
    congruence.
  Qed.
  
  Lemma sorted_Prefix_in_eq :
    forall l' l,
      sorted l ->
      Prefix l' l ->
      (forall e, In e l -> In e l') ->
      l' = l.
  Proof.
    induction l'; intros; simpl in *; intuition.
    - destruct l; simpl in *; auto.
      specialize (H1 e); intuition.
    - break_match; intuition. subst.
      simpl in *. intuition. f_equal.
      eapply IHl'; eauto.
      intros.
      specialize (H1 e0); intuition.
      subst. specialize (H0 e0); intuition. omega.
  Qed.

  Lemma removeAfterIndex_eq :
    forall l i,
      (forall e, In e l -> eIndex e <= i) ->
      removeAfterIndex l i = l.
  Proof.
    induction l; intros; simpl in *; intuition.
    break_if; intuition.
    do_bool. specialize (H a). intuition. omega.
  Qed.

  Lemma removeAfterIndex_in_app :
    forall l l' e,
      In e l ->
      removeAfterIndex (l ++ l') (eIndex e) =
      (removeAfterIndex l (eIndex e)) ++ l'.
  Proof.
    induction l; intros; simpl in *; intuition;
    subst; break_if; do_bool; eauto using app_ass.
    omega.
  Qed.

  Lemma removeAfterIndex_in_app_l' :
    forall l l' e,
      (forall e', In e' l -> eIndex e' > eIndex e) ->
      In e l' ->
      removeAfterIndex (l ++ l') (eIndex e) =
      removeAfterIndex l' (eIndex e).
  Proof.
    induction l; intros; simpl in *; intuition;
    subst; break_if; do_bool; eauto using app_ass.
    specialize (H a). intuition. omega.
  Qed.

  Lemma removeAfterIndex_maxIndex_sorted :
    forall l,
      sorted l ->
      l = removeAfterIndex l (maxIndex l).
  Proof.
    intros; induction l; simpl in *; intuition.
    break_if; auto. do_bool. omega.
  Qed.
  
End CommonTheorems.

Notation is_append_entries m :=
  (exists t n prevT prevI entries c,
     m = AppendEntries t n prevT prevI entries c).

Notation is_request_vote_reply m :=
  (exists t r,
     m = RequestVoteReply t r).

Ltac use_applyEntries_spec :=
  match goal with
    | H : context [applyEntries] |- _ => eapply applyEntries_spec in H; eauto; break_exists
  end.
