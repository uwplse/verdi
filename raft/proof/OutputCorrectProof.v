Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import TraceRelations.

Require Import Raft.
Require Import CommonTheorems.
Require Import OutputCorrectInterface.
Require Import AppliedEntriesMonotonicInterface.
Require Import TraceUtil.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Section OutputCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {aemi : applied_entries_monotonic_interface}.

  Section inner.
  Variables client id : nat.
  Variable out : output.
  
  Theorem in_output_trace_dec :
    forall tr : list (name * (raft_input + list raft_output)),
      {in_output_trace client id out tr} + {~ in_output_trace client id out tr}.
  Proof.
    unfold in_output_trace.
    intros.
    destruct (find (fun p => match snd p with
                               | inr l => match find (is_client_response client id out) l with
                                            | Some x => true
                                            | None => false
                                          end
                               | _ => false
                             end) tr) eqn:?.
    - find_apply_lem_hyp find_some. break_and.
      repeat break_match; try discriminate.
      find_apply_lem_hyp find_some. break_and.
      unfold is_client_response, in_output_list in *.
      break_match; try discriminate. do_bool. break_and. do_bool. subst.
      left. exists l, (fst p). clean.
      break_and. do_bool.
      break_if; try congruence. subst. intuition.
      find_reverse_rewrite.
      rewrite <- surjective_pairing.
      auto.
    - right. intro. break_exists. break_and.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. break_match; try discriminate.
      unfold in_output_list in *. break_exists.
      find_eapply_lem_hyp find_none; eauto.
      simpl in *. find_apply_lem_hyp Bool.andb_false_elim.
      repeat (intuition; do_bool).
      break_if; congruence.
  Qed.

  Lemma in_output_changed :
    forall tr out o,
      ~ in_output_trace client id out tr ->
      in_output_trace client id out (tr ++ o) ->
      in_output_trace client id out o.
  Proof.
    intros. unfold in_output_trace in *.
    break_exists_exists.
    intuition. do_in_app; intuition.
    exfalso. eauto.
  Qed.

  Lemma in_output_list_split :
    forall l l',
      in_output_list client id out (l ++ l') ->
      in_output_list client id out l \/ in_output_list client id out l'.
  Proof.
    intros.
    unfold in_output_list in *.
    break_exists; do_in_app; intuition eauto.
  Qed.

  Lemma in_output_list_empty :
    ~ in_output_list client id out [].
  Proof.
    intuition.
  Qed.

  Lemma doLeader_key_in_output_list :
    forall st h os st' m,
      doLeader st h = (os, st', m) ->
      ~ in_output_list client id out os.
  Proof.
    intros. unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty.
  Qed.

  Lemma handleInput_key_in_output_list :
    forall st h i os st' m,
      handleInput h i st = (os, st', m) ->
      ~ in_output_list client id out os.
  Proof.
    intros. unfold handleInput, handleTimeout, handleClientRequest, tryToBecomeLeader in *.
    repeat break_match; find_inversion; intuition eauto using in_output_list_empty;
    unfold in_output_list in *; break_exists; simpl in *; intuition; congruence.
  Qed.

  Ltac update_destruct :=
    match goal with
      | [ |- context [ update _ ?y _ ?x ] ] => destruct (name_eq_dec y x)
    end.

  Lemma deduplicate_log'_app :
    forall l l' ks,
      exists l'',
        deduplicate_log' (l ++ l') ks = deduplicate_log' l ks ++ l''.
  Proof.
    induction l; intros; simpl in *; eauto.
    break_if; eauto.
    specialize (IHl l' (key_of a :: ks)).
    break_exists_exists. simpl. f_equal. intuition.
  Qed.

  Lemma deduplicate_log_app :
    forall l l',
      exists l'',
        deduplicate_log (l ++ l') = deduplicate_log l ++ l''.
  Proof.
    eauto using deduplicate_log'_app.
  Qed.
  
  Instance TR : TraceRelation step_f :=
    {
      init := step_f_init;
      T := in_output_trace client id out ;
      T_dec := in_output_trace_dec ;
      R := fun s => let (_, net) := s in
                   exists xs e ys tr' st' i,
                     deduplicate_log (applied_entries (nwState net)) = xs ++ e :: ys /\
                     eClient e = client /\
                     eId e = id /\
                     eInput e = i /\
                     execute_log (xs ++ [e]) = (tr', st') /\
                     hd_error (rev tr') = Some (i, out)
    }.
  Proof.
    - intros. repeat break_let. subst.
      find_eapply_lem_hyp applied_entries_monotonic';
        eauto using step_f_star_raft_intermediate_reachable.
      break_exists.
      repeat find_rewrite.
      match goal with
          | [ |- context [ deduplicate_log (?l ++ ?l') ] ] =>
            pose proof deduplicate_log_app l l'; break_exists; find_rewrite
      end.
      repeat eexists; intuition eauto; repeat find_rewrite; auto.
      rewrite app_ass. simpl. repeat f_equal.
  - unfold in_output_trace in *. intuition.
    break_exists; intuition.
  - intros.
    break_let. subst.
    find_apply_lem_hyp in_output_changed; auto.
    admit.
  Defined.
  End inner.
End OutputCorrect.
