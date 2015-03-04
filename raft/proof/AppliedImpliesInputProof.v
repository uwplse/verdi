Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.
Require Import InverseTraceRelations.

Require Import Raft.
Require Import CommonTheorems.
Require Import TraceUtil.
Require Import OutputImpliesAppliedInterface.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import AppliedImpliesInputInterface.

Section AppliedImpliesInputProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {oiai : output_implies_applied_interface}.

  Lemma in_input_trace_or_app :
    forall c id i tr1 tr2,
      in_input_trace c id i tr1 \/ in_input_trace c id i tr2 ->
      in_input_trace c id i (tr1 ++ tr2).
  Proof.
    unfold in_input_trace.
    intuition; break_exists_exists; intuition.
  Qed.

  Section inner.
    Variables client id : nat.
    Variable i : input.

    Lemma applied_implies_input_update_split :
      forall client id i net h d ps,
        applied_implies_input_state client id i (mkNetwork ps (update (nwState net) h d)) ->
        exists e,
          correct_entry client id i e /\
          (In e (log d) \/
           (exists h, In e (log (nwState net h))) \/
           (exists p es, In p ps /\ mEntries (pBody p) = Some es /\ In e es)).
    Proof.
      unfold applied_implies_input_state.
      intros.
      break_exists_exists.
      intuition.
      break_exists.
      simpl in *.
      destruct (name_eq_dec h x0); rewrite_update; eauto.
    Qed.

    Lemma aiis_intro_state :
      forall client id i net e h,
        In e (log (nwState net h)) ->
        correct_entry client id i e ->
        applied_implies_input_state client id i net.
    Proof.
      unfold applied_implies_input_state.
      eauto 10.
    Qed.

    Lemma aiis_intro_packet :
      forall client id i net e p es,
        mEntries (pBody p) = Some es ->
        In p (nwPackets net) ->
        correct_entry client id i e ->
        In e es ->
        applied_implies_input_state client id i net.
    Proof.
      unfold applied_implies_input_state.
      eauto 10.
    Qed.

    Lemma doGenericServer_log :
      forall h st os st' ps,
        doGenericServer h st = (os, st', ps) ->
        log st' = log st.
    Proof.
      intros. unfold doGenericServer in *.
      repeat break_match; find_inversion;
      use_applyEntries_spec; simpl in *;
      subst; auto.
    Qed.

    Theorem handleTimeout_log :
      forall h st out st' ps,
        handleTimeout h st = (out, st', ps) ->
        log st' = log st.
    Proof.
      intros. unfold handleTimeout, tryToBecomeLeader in *.
      break_match; find_inversion; subst; auto.
    Qed.

    Theorem handleClientRequest_no_messages :
      forall h st client id c out st' ps p,
        handleClientRequest h st client id c = (out, st', ps) ->
        In p ps -> False.
    Proof.
      unfold handleClientRequest.
      intros.
      break_match; find_inversion; simpl in *; intuition.
    Qed.

    Theorem handleClientRequest_log :
      forall h st client id c out st' ps,
        handleClientRequest h st client id c = (out, st', ps) ->
        (log st' = log st \/
         exists e,
           log st' = e :: log st /\
           eIndex e = S (maxIndex (log st)) /\
           eTerm e = currentTerm st /\
           eClient e = client /\
           eInput e = c /\
           eId e = id).
    Proof.
      intros. unfold handleClientRequest in *.
      break_match; find_inversion; subst; intuition.
      simpl in *. eauto 10.
    Qed.

    Theorem handleTimeout_not_is_append_entries :
      forall h st st' ms m,
        handleTimeout h st = (st', ms) ->
        In m ms -> ~ is_append_entries (snd m).
    Proof.
      intros. unfold handleTimeout, tryToBecomeLeader in *.
      break_match; find_inversion; subst; simpl in *; eauto;
      repeat (do_in_map; subst; simpl in *); intuition; break_exists; congruence.
    Qed.

    Lemma mEntries_some_is_applied_entries :
      forall m es,
        mEntries m = Some es ->
        is_append_entries m.
    Proof.
      unfold mEntries.
      intros.
      break_match; try discriminate.
      find_inversion.
      eauto 10.
    Qed.

    Lemma doGenericServer_packets :
      forall h st os st' ps p,
        doGenericServer h st = (os, st', ps) ->
        In p ps -> False.
    Proof.
      intros. unfold doGenericServer in *.
      repeat break_match; find_inversion; subst; auto.
    Qed.

    Lemma doLeader_messages :
      forall d h os d' ms m es e,
        doLeader d h = (os, d', ms) ->
        In m ms ->
        mEntries (snd m) = Some es ->
        In e es ->
        In e (log d).
    Proof.
      unfold doLeader.
      intros.
      repeat break_match; repeat find_inversion; simpl in *; intuition.
      do_in_map. subst. simpl in *. find_inversion.
      eauto using findGtIndex_in.
    Qed.

    Lemma handleInputs_aais :
      forall client id h inp i net os d' ms e o,
        ~ applied_implies_input_state client id i net ->
        handleInput h inp (nwState net h) = (os, d', ms) ->
        correct_entry client id i e ->
        In e (log d') ->
        in_input_trace client id i [(h, inl inp); o].
    Proof.
      intros.
      destruct inp; simpl in *.
      - find_erewrite_lem handleTimeout_log.
        exfalso. eauto using aiis_intro_state.
      - find_eapply_lem_hyp handleClientRequest_log.
        break_or_hyp.
        + find_rewrite.
          exfalso. eauto using aiis_intro_state.
        + break_exists. break_and. subst.
          find_rewrite. simpl in *.
          break_or_hyp.
          * subst. unfold in_input_trace. unfold correct_entry in *.
            break_and. subst. simpl. eauto.
          * exfalso. eauto using aiis_intro_state.
    Qed.

    Lemma handleMessage_aais :
      forall client id i net p d' ms e,
        In p (nwPackets net) ->
        handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d', ms) ->
        correct_entry client id i e ->
        In e (log d') ->
        In e (log (nwState net (pDst p))).
    Admitted.

    Lemma handleMessage_sends_log :
      forall client id i net p d' ms m es e,
        In p (nwPackets net) ->
        handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d', ms) ->
        correct_entry client id i e ->
        In m ms ->
        mEntries (snd m) = Some es ->
        In e es ->
        In e (log (nwState net (pDst p))).
    Admitted.

    Lemma applied_implies_input_in_input_trace :
      forall net failed net' failed' tr,
        raft_intermediate_reachable net ->
        @step_f _ _ failure_params (failed, net) (failed', net') tr ->
        ~ applied_implies_input_state client id i net ->
        applied_implies_input_state client id i net' ->
        in_input_trace client id i tr.
    Proof.
      intros.
      match goal with
        | [ H : context [step_f _ _ _ ] |- _ ] => invcs H
      end.
      - unfold RaftNetHandler in *. repeat break_let. subst. find_inversion.
        find_apply_lem_hyp applied_implies_input_update_split.
        break_exists. intuition; break_exists.
        + find_erewrite_lem doLeader_same_log.
          find_erewrite_lem doGenericServer_log.
          exfalso. eauto using aiis_intro_state, handleMessage_aais.
        + exfalso. eauto using aiis_intro_state.
        + intuition. do_in_app. intuition.
          * do_in_map. subst. simpl in *.
            { repeat (do_in_app; intuition).
              - exfalso. eauto using aiis_intro_state, handleMessage_sends_log.
              - exfalso. eauto using doGenericServer_packets.
              - find_eapply_lem_hyp doLeader_messages; eauto.
                find_erewrite_lem doGenericServer_log.
                exfalso. eauto using aiis_intro_state, handleMessage_aais.
            }
          * exfalso. eauto using aiis_intro_packet.
      - unfold RaftInputHandler in *. repeat break_let. subst. find_inversion.
        find_apply_lem_hyp applied_implies_input_update_split.
        break_exists. intuition; break_exists.
        + find_erewrite_lem doLeader_same_log.
          find_erewrite_lem doGenericServer_log.
          eauto using handleInputs_aais.
        + exfalso. eauto using aiis_intro_state.
        + intuition. do_in_app. intuition.
          * do_in_map. subst. simpl in *.
            { repeat (do_in_app; intuition).
              - destruct inp; simpl in *.
                + exfalso. eapply handleTimeout_not_is_append_entries; eauto.
                  eauto using mEntries_some_is_applied_entries.
                + exfalso. eauto using handleClientRequest_no_messages.
              - exfalso. eauto using doGenericServer_packets.
              - find_eapply_lem_hyp doLeader_messages; eauto.
                find_erewrite_lem doGenericServer_log.
                eauto using handleInputs_aais.
            }
          * exfalso. eauto using aiis_intro_packet.
      - unfold applied_implies_input_state in H2.
        break_exists. intuition; break_exists; simpl in *.
        + exfalso; eauto  using aiis_intro_state.
        + break_and. simpl in *.
          exfalso. eauto using aiis_intro_packet.
      - unfold applied_implies_input_state in H2.
        break_exists. intuition; break_exists; simpl in *.
        + exfalso; eauto  using aiis_intro_state.
        + intuition.
          * subst. exfalso. eauto using aiis_intro_packet.
          * exfalso. apply H1. eapply aiis_intro_packet; eauto.
            congruence.
      - congruence.
      - unfold applied_implies_input_state in H2.
        break_exists. intuition; break_exists; simpl in *.
        + break_if.
          * subst. unfold reboot in *. simpl in *.
            exfalso. eauto using aiis_intro_state.
          * exfalso. eauto using aiis_intro_state.
        + intuition.
          exfalso. eauto using aiis_intro_packet.
    Qed.

    Instance ITR : InverseTraceRelation step_f :=
      { init := step_f_init;
        R := fun s => applied_implies_input_state client id i (snd s);
        T := in_input_trace client id i
      }.
    - intros. admit.  (* decidable R *)
    - intros.
      unfold in_input_trace in *. break_exists_exists.
      intuition.
    - unfold applied_implies_input_state. intro. break_exists. break_and.
      intuition; break_exists; intuition.
    - intros. simpl in *.
      apply in_input_trace_or_app. right.
      destruct s, s'. simpl in *.
      eapply applied_implies_input_in_input_trace; eauto.
      eapply step_f_star_raft_intermediate_reachable; eauto.
    Defined.
  End inner.

  Lemma applied_implies_input :
    forall client id failed net tr e,
      @step_f_star _ _ failure_params step_f_init (failed, net) tr ->
      eClient e = client ->
      eId e = id ->
      applied_implies_input_state client id (eInput e) net ->
      in_input_trace client id (eInput e) tr.
  Proof.
    intros.
    pose proof @inverse_trace_relations_work _ _ step_f (ITR client id (eInput e)) (failed, net) tr.
    unfold step_f_star in *. simpl in *.
    auto.
  Qed.

  Instance aiii : applied_implies_input_interface.
  Proof.
    split.
    exact applied_implies_input.
  Qed.
End AppliedImpliesInputProof.
