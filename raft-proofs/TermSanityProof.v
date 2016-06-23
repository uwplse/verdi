Require Import Raft.
Require Import CommonTheorems.

Require Import TermSanityInterface.

Section TermSanityProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Theorem no_entries_past_current_term_nw_packets_unchanged :
    forall net ps' st',
      no_entries_past_current_term_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ False) ->
      no_entries_past_current_term_nw (mkNetwork ps' st').
  Proof.
    unfold no_entries_past_current_term_nw in *. intros.
    simpl in *. find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem no_entries_past_current_term_nw_only_new_packets_matter :
    forall net ps' l st',
      no_entries_past_current_term_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p l) ->
      no_entries_past_current_term_nw (mkNetwork l st') ->
      no_entries_past_current_term_nw (mkNetwork ps' st').
  Proof.
    unfold no_entries_past_current_term_nw. intros. simpl in *.
    find_apply_hyp_hyp. intuition eauto.
  Qed.

  Theorem no_entries_past_current_term_nw_no_append_entries :
    forall net ps' h l st',
      no_entries_past_current_term_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ In p (send_packets h l)) ->
      (forall m, In m l -> ~ is_append_entries (snd m)) ->
      no_entries_past_current_term_nw (mkNetwork ps' st').
  Proof.
    intros. eapply no_entries_past_current_term_nw_only_new_packets_matter; eauto.
    unfold no_entries_past_current_term_nw. intros. simpl in *.
    do_in_map. subst. simpl in *.
    find_apply_hyp_hyp.
    exfalso. match goal with H : _ |- _ => apply H end.
    repeat eexists; eauto.
  Qed.

  Theorem no_entries_past_current_term_nw_not_append_entries :
    forall net ps' p' st',
      no_entries_past_current_term_nw net ->
      (forall p, In p ps' -> In p (nwPackets net) \/ p = p') ->
      ~ is_append_entries (pBody p') ->
      no_entries_past_current_term_nw (mkNetwork ps' st').
  Proof.
    intros.
    unfold no_entries_past_current_term_nw. intros. simpl in *. find_apply_hyp_hyp.
    intuition.
    - unfold no_entries_past_current_term_nw in *. eauto.
    - subst. exfalso. match goal with H : _ |- _ => apply H end.
      repeat eexists; eauto.
  Qed.

  Theorem no_entries_past_current_term_init :
    raft_net_invariant_init (no_entries_past_current_term).
  Proof.
    unfold raft_net_invariant_init, no_entries_past_current_term.
    intuition.
    - unfold no_entries_past_current_term_host.
      intros. simpl in *. intuition.
    - unfold no_entries_past_current_term_nw.
      intros. simpl in *. intuition.
  Qed.

  Lemma doLeader_spec :
    forall h st os st' ps,
      doLeader st h = (os, st', ps) ->
      log st' = log st /\ currentTerm st' = currentTerm st.
  Proof.
    intros. unfold doLeader in *.
    repeat break_match; find_inversion; subst; auto.
  Qed.

  Theorem no_entries_past_current_term_do_leader :
    raft_net_invariant_do_leader (no_entries_past_current_term).
  Proof.
    unfold raft_net_invariant_do_leader, no_entries_past_current_term.
    intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *.
      find_apply_lem_hyp doLeader_spec.
      find_higher_order_rewrite.
      break_if;
        subst; intuition;
        repeat find_rewrite;
        eauto.
    - unfold no_entries_past_current_term_nw in *. intros; simpl in *.
      find_apply_hyp_hyp. intuition eauto.
      unfold doLeader in *.
      repeat break_match; repeat find_inversion; try solve_by_inversion.
      repeat do_in_map; subst; simpl in *; find_inversion.
      find_apply_lem_hyp findGtIndex_in. eauto.
  Qed.

  Lemma doGenericServer_spec :
    forall h d os d' ms,
      doGenericServer h d = (os, d', ms) ->
      (log d' = log d /\ currentTerm d' = currentTerm d /\
       (forall m, In m ms -> ~ is_append_entries (snd m))).
  Proof.
    intros. unfold doGenericServer in *.
    repeat break_match; find_inversion; subst; intuition;
    use_applyEntries_spec; subst; simpl in *; auto.
  Qed.

  Lemma no_entries_past_current_term_do_generic_server :
    raft_net_invariant_do_generic_server no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_do_generic_server, no_entries_past_current_term. intros.
    find_apply_lem_hyp doGenericServer_spec. intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *.
      find_higher_order_rewrite; break_match; eauto.
      subst; repeat find_rewrite; eauto.
    - eauto using no_entries_past_current_term_nw_no_append_entries.
  Qed.


  Lemma handleClientRequest_messages :
    forall h d client id c os d' ms,
      handleClientRequest h d client id c = (os, d', ms) ->
      (forall m, In m ms -> ~ is_append_entries (snd m)).
  Proof.
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; intuition.
  Qed.

  Lemma no_entries_past_current_term_client_request :
    raft_net_invariant_client_request (no_entries_past_current_term).
  Proof.
    unfold raft_net_invariant_client_request, no_entries_past_current_term.
    intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *.
      find_higher_order_rewrite; break_if; eauto.
      unfold handleClientRequest in *.
      subst.
      break_match; find_inversion; eauto.
      simpl in *. intuition. subst; simpl in *; auto.
    - eauto using no_entries_past_current_term_nw_no_append_entries,
                  handleClientRequest_messages.
  Qed.


  Lemma handleTimeout_spec :
    forall h d os d' ms,
      handleTimeout h d = (os, d', ms) ->
      log d' = log d /\ currentTerm d <= currentTerm d' /\
      ( forall m, In m ms -> ~ is_append_entries (snd m)).
  Proof.
    intros. unfold handleTimeout, tryToBecomeLeader in *.
    repeat break_match; find_inversion; subst; intuition;
    do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma no_entries_past_current_term_timeout :
    raft_net_invariant_timeout no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_timeout, no_entries_past_current_term.
    intros. find_apply_lem_hyp handleTimeout_spec.
    intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *.
      find_higher_order_rewrite; break_if; eauto.
      subst; repeat find_rewrite.
      eapply le_trans; [|eauto]; eauto.
    - eauto using no_entries_past_current_term_nw_no_append_entries.
  Qed.

  Lemma handleAppendEntries_spec :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      (currentTerm st <= currentTerm st' /\
       (forall e,
          In e (log st') ->
          In e (log st) \/
          In e es /\ currentTerm st' = t) /\
       ~ is_append_entries m).
  Proof.
    intros.
    unfold handleAppendEntries, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try solve [break_exists; congruence];
    in_crush; eauto using removeAfterIndex_in.
  Qed.

  Lemma no_entries_past_current_term_append_entries :
    raft_net_invariant_append_entries no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_append_entries, no_entries_past_current_term.
    intros. find_apply_lem_hyp handleAppendEntries_spec.
    intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *. find_higher_order_rewrite.
      break_if; eauto. subst.
      find_apply_hyp_hyp. intuition.
      + eapply le_trans; [|eauto]; eauto.
      + subst.
        eapply_prop no_entries_past_current_term_nw; eauto.
    - match goal with
        | _ : context [{| pSrc := ?ps; pDst := ?pd; pBody := ?pb |}] |- _ =>
          eapply no_entries_past_current_term_nw_not_append_entries
          with (p' := {| pSrc := ps; pDst := pd; pBody := pb |})
      end; eauto.
     intros. find_apply_hyp_hyp. find_rewrite. in_crush.
  Qed.

  Lemma no_entries_past_current_term_unaffected :
    forall net st' ps' xs p ys d ms,
      nwPackets net = xs ++ p :: ys ->
      no_entries_past_current_term net ->
      (forall h : Net.name, st' h = update (nwState net) (pDst p) d h) ->
      (forall p' : packet,
       In p' ps' ->
       In p' (xs ++ ys) \/ In p' (send_packets (pDst p) ms)) ->
      currentTerm (nwState net (pDst p)) <= currentTerm d ->
      log d = log (nwState net (pDst p)) ->
      (forall m, In m ms -> ~ is_append_entries (snd m)) ->
      no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
  Proof.
    intros. unfold no_entries_past_current_term in *. intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *. find_higher_order_rewrite.
      break_if; eauto. subst.
      repeat find_rewrite. eapply le_trans; [|eauto].
      eauto.
    - unfold no_entries_past_current_term_nw.
      intros. simpl in *.
      find_apply_hyp_hyp. intuition.
      + intros.
        match goal with
          | _ : In ?p _ |- _ =>
            assert (In p (nwPackets net)) by (find_rewrite; in_crush)
        end.
        eapply_prop no_entries_past_current_term_nw; eauto.
      + exfalso.
        do_in_map. subst.
        simpl in *.
        find_apply_hyp_hyp. find_rewrite. repeat eexists; eauto.
  Qed.

  Lemma no_entries_past_current_term_unaffected_1 :
    forall net st' ps' xs p ys d m,
      nwPackets net = xs ++ p :: ys ->
      no_entries_past_current_term net ->
      (forall h : Net.name, st' h = update (nwState net) (pDst p) d h) ->
      (forall p' : packet,
       In p' ps' ->
       In p' (xs ++ ys) \/ p' = m) ->
      currentTerm (nwState net (pDst p)) <= currentTerm d ->
      log d = log (nwState net (pDst p)) ->
      ~ is_append_entries (pBody m) ->
      no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
  Proof.
    intros. unfold no_entries_past_current_term in *. intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *. find_higher_order_rewrite.
      break_if; eauto. subst.
      repeat find_rewrite. eapply le_trans; [|eauto].
      eauto.
    - unfold no_entries_past_current_term_nw.
      intros. simpl in *.
      find_apply_hyp_hyp. intuition.
      + intros.
        match goal with
          | _ : In ?p _ |- _ =>
            assert (In p (nwPackets net)) by (find_rewrite; in_crush)
        end.
        eapply_prop no_entries_past_current_term_nw; eauto.
      + exfalso. subst. repeat find_rewrite.
        forwards; intuition.
        repeat eexists; eauto.
  Qed.

  Lemma no_entries_past_current_term_unaffected_0 :
    forall net st' ps' xs p ys d,
      nwPackets net = xs ++ p :: ys ->
      no_entries_past_current_term net ->
      (forall h : Net.name, st' h = update (nwState net) (pDst p) d h) ->
      (forall p' : packet,
       In p' ps' ->
       In p' (xs ++ ys)) ->
      currentTerm (nwState net (pDst p)) <= currentTerm d ->
      log d = log (nwState net (pDst p)) ->
      no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
  Proof.
    intros. unfold no_entries_past_current_term in *. intuition.
    - unfold no_entries_past_current_term_host in *.
      intros. simpl in *. find_higher_order_rewrite.
      break_if; eauto. subst.
      repeat find_rewrite. eapply le_trans; [|eauto].
      eauto.
    - unfold no_entries_past_current_term_nw.
      intros. simpl in *.
      find_apply_hyp_hyp.
      match goal with
        | _ : In ?p _ |- _ =>
          assert (In p (nwPackets net)) by (find_rewrite; in_crush)
      end.
      eapply_prop no_entries_past_current_term_nw; eauto.
  Qed.

  Lemma handleAppendEntriesReply_spec :
    forall h st h' t es r st' ms,
      handleAppendEntriesReply h st h' t es r = (st', ms) ->
      (currentTerm st <= currentTerm st' /\
       log st' = log st /\
       (forall m, In m ms -> ~ is_append_entries (snd m))).
  Proof.
    intros.
    unfold handleAppendEntriesReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try solve [break_exists; congruence];
    in_crush; eauto using removeAfterIndex_in.
  Qed.

  Lemma no_entries_past_current_term_append_entries_reply :
    raft_net_invariant_append_entries_reply no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_append_entries_reply.
    intros. find_apply_lem_hyp handleAppendEntriesReply_spec.
    intuition eauto using no_entries_past_current_term_unaffected.
  Qed.

  Lemma handleRequestVote_spec :
    forall h st t h' pli plt st' m,
      handleRequestVote h st t h' pli plt = (st', m) ->
      (currentTerm st <= currentTerm st' /\
       log st' = log st /\
       ~ is_append_entries m).
  Proof.
    intros.
    unfold handleRequestVote, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try solve [break_exists; congruence];
    in_crush; eauto using removeAfterIndex_in.
  Qed.

  Lemma no_entries_past_current_term_request_vote :
    raft_net_invariant_request_vote no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_request_vote.
    intros. find_apply_lem_hyp handleRequestVote_spec.
    intuition eauto using no_entries_past_current_term_unaffected_1.
  Qed.

  Lemma handleRequestVoteReply_spec :
    forall h st h' t v st',
      handleRequestVoteReply h st h' t v = st' ->
      (currentTerm st <= currentTerm st' /\
       log st' = log st).
  Proof.
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition.
  Qed.

  Lemma no_entries_past_current_term_request_vote_reply :
    raft_net_invariant_request_vote_reply no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_request_vote_reply.
    intros. find_apply_lem_hyp handleRequestVoteReply_spec.
    intuition eauto using no_entries_past_current_term_unaffected_0.
  Qed.

  Lemma no_entries_past_current_term_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_state_same_packet_subset,
    no_entries_past_current_term, no_entries_past_current_term_host,
    no_entries_past_current_term_nw.
    intros. intuition.
    - repeat find_reverse_higher_order_rewrite. eauto.
    - find_apply_hyp_hyp. eauto.
  Qed.

  Lemma no_entries_past_current_term_reboot :
    raft_net_invariant_reboot no_entries_past_current_term.
  Proof.
    unfold raft_net_invariant_reboot,
    no_entries_past_current_term, no_entries_past_current_term_host,
    no_entries_past_current_term_nw, reboot.
    intuition.
    - repeat find_higher_order_rewrite. simpl in *.
      subst. break_if; simpl in *; intuition.
     - find_reverse_rewrite. eauto.
  Qed.

  Theorem no_entries_past_current_term_invariant :
    forall net,
      raft_intermediate_reachable net ->
      no_entries_past_current_term net.
  Proof.
    intros.
    eapply raft_net_invariant; eauto.
    - apply no_entries_past_current_term_init.
    - apply no_entries_past_current_term_client_request.
    - apply no_entries_past_current_term_timeout.
    - apply no_entries_past_current_term_append_entries.
    - apply no_entries_past_current_term_append_entries_reply.
    - apply no_entries_past_current_term_request_vote.
    - apply no_entries_past_current_term_request_vote_reply.
    - apply no_entries_past_current_term_do_leader.
    - apply no_entries_past_current_term_do_generic_server.
    - apply no_entries_past_current_term_state_same_packet_subset.
    - apply no_entries_past_current_term_reboot.
  Qed.

  Instance tsi : term_sanity_interface.
  Proof.
    split.
    auto using no_entries_past_current_term_invariant.
  Qed.
End TermSanityProof.
