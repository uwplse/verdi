Require Import FunctionalExtensionality.

Require Import Raft.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Require Import DecompositionWithPostState.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import AppendEntriesRequestReplyCorrespondenceInterface.

Require Import DupDropReordering.

Section AppendEntriesRequestReplyCorrespondence.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma append_entries_request_reply_correspondence_init :
    raft_net_invariant_init append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *. intuition.
  Qed.

  Lemma append_entries_request_reply_correspondence_timeout :
    raft_net_invariant_timeout append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto.
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli.
      break_exists_name plt.
      break_exists_name ci.
      break_exists_name n.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p) (pSrc p) (AppendEntries t n pli plt es ci)]) st').
      subst.
      exists pli,plt,ci,n. simpl in *; intuition.
      eapply RIR_handleInput with (net0 := net') (inp := Timeout); eauto;
      simpl; repeat find_rewrite; eauto.
      intros.
      do_in_app. intuition.
      find_apply_hyp_hyp.
      intuition.
    - exfalso.
      do_in_map. subst. simpl in *.
      unfold handleTimeout, tryToBecomeLeader in *.
      repeat break_match; find_inversion; intuition; do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma append_entries_request_reply_correspondence_client_request :
    raft_net_invariant_client_request append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto.
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli.
      break_exists_name plt.
      break_exists_name ci.
      break_exists_name n.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p) (pSrc p) (AppendEntries t n pli plt es ci)]) st').
      subst.
      exists pli,plt,ci,n. simpl in *; intuition.
      eapply RIR_handleInput with (net0 := net') (inp := ClientRequest client id c); eauto;
      simpl; repeat find_rewrite; eauto.
      intros.
      do_in_app. intuition.
      find_apply_hyp_hyp.
      intuition.
    - exfalso.
      do_in_map. subst. simpl in *.
      unfold handleClientRequest in *.
      repeat break_match; find_inversion; intuition; do_in_map; subst; simpl in *; congruence.
  Qed.


  Lemma append_entries_request_reply_correspondence_do_leader :
    raft_net_invariant_do_leader append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto.
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli.
      break_exists_name plt.
      break_exists_name ci.
      break_exists_name n.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p) (pSrc p) (AppendEntries t n pli plt es ci)]) st').
      subst.
      exists pli,plt,ci,n. simpl in *; intuition.
      eapply RIR_doLeader with (net0 := net'); eauto;
      simpl; repeat find_rewrite; eauto.
      intros.
      do_in_app. intuition.
      find_apply_hyp_hyp.
      intuition.
    - exfalso.
      do_in_map. subst. simpl in *.
      unfold doLeader in *.
      repeat break_match; find_inversion; intuition; do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma append_entries_request_reply_correspondence_do_generic_server :
    raft_net_invariant_do_generic_server append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto.
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli.
      break_exists_name plt.
      break_exists_name ci.
      break_exists_name n.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p) (pSrc p) (AppendEntries t n pli plt es ci)]) st').
      subst.
      exists pli,plt,ci,n. simpl in *; intuition.
      eapply RIR_doGenericServer with (net0 := net'); eauto;
      simpl; repeat find_rewrite; eauto.
      intros.
      do_in_app. intuition.
      find_apply_hyp_hyp.
      intuition.
    - exfalso.
      do_in_map. subst. simpl in *.
      unfold doGenericServer in *.
      repeat break_match; find_inversion; intuition; do_in_map; subst; simpl in *; congruence.
  Qed.

  Lemma append_entries_request_reply_correspondence_reboot :
    raft_net_invariant_reboot append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_reverse_rewrite.
    find_apply_hyp_hyp.
    unfold exists_equivalent_network_with_aer in *.
    break_exists_name net''.
    break_exists_name pli.
    break_exists_name plt.
    break_exists_name ci.
    break_exists_name n.
    intuition. subst.
    remember mkNetwork as mkN.
    remember mkPacket as mkP.
    unfold Net.name in *. simpl in *.
    exists (mkN ((nwPackets net) ++ [mkP (pDst p) (pSrc p) (AppendEntries t n pli plt es ci)]) (nwState net')).
    subst.
    exists pli,plt,ci,n. simpl in *; repeat find_rewrite; intuition.
    eapply RIR_step_f with (net0 := net''); [|eapply SF_reboot with (h0 := h) (failed := [h])]; eauto;
    simpl; repeat find_rewrite; eauto.
    f_equal.
    apply functional_extensionality.
    intros. repeat find_higher_order_rewrite.
    unfold update. repeat break_if; subst; eauto; congruence.
  Qed.

  
  
  Lemma subset_reachable :
    forall net net',
      nwState net' = nwState net ->
      (forall p, In p (nwPackets net') -> In p (nwPackets net)) ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable net'.
  Proof.
    intros.
    pose proof dup_drop_reorder _ packet_eq_dec _ _ ltac:(eauto).
    match goal with
    | [ H : dup_drop_step_star _ _ _ |- _ ] =>
      eapply step_f_dup_drop_step with (f := []) (Sigma := nwState net) in H
    end.
    eapply step_f_star_raft_intermediate_reachable_extend with (f := []) (f' := []) (tr := []); [|eauto].
    destruct net, net'. simpl in *. subst.
    auto.
  Qed.
  
  Lemma append_entries_request_reply_correspondence_state_same_packet_subset :
    raft_net_invariant_state_same_packet_subset append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    unfold exists_equivalent_network_with_aer in *.
    break_exists_name net''.
    break_exists_name pli.
    break_exists_name plt.
    break_exists_name ci.
    break_exists_name n.
    intuition.
    (exists (mkNetwork (nwPackets net' ++ [{|
      pSrc := pDst p;
      pDst := pSrc p;
      pBody := AppendEntries t n pli plt es ci |}]) (nwState net'))).
    repeat eexists; intuition; eauto.
    repeat find_rewrite.
    break_exists_exists; intuition; repeat find_rewrite; eauto.
    eapply subset_reachable with (net := net''); eauto.
    - simpl in *. repeat find_rewrite.
      apply functional_extensionality. eauto.
    - simpl.
      intros. repeat find_rewrite. do_in_app. intuition.
  Qed.
  
  Lemma handleAppendEntries_reply_spec:
    forall h st (d : raft_data) 
      (t : term) (n : name) (pli : logIndex) (plt : term) 
      (es : list entry) (ci : logIndex) (t0 : term) 
      (es0 : list entry) t' es',
      handleAppendEntries h st t n pli plt es ci =
      (d, AppendEntriesReply t' es' true) ->
      t' = t /\ es' = es.
  Proof.
    intros.
    unfold handleAppendEntries in *.
    repeat break_match; find_inversion; auto; congruence.
  Qed.
  
  Lemma append_entries_request_reply_correspondence_append_entries :
    raft_net_invariant_append_entries append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto; [|repeat find_rewrite; in_crush].
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli'.
      break_exists_name plt'.
      break_exists_name ci'.
      break_exists_name n'.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p0) (pSrc p0) (AppendEntries t0 n' pli' plt' es0 ci')]) st').
      subst.
      exists pli',plt',ci',n'. simpl in *; intuition.
      repeat find_rewrite.
      match goal with
        | H : nwPackets net' = (?xs ++ ?p :: ?ys) ++ ?l |- _ =>
          assert (nwPackets net' = xs ++ p :: (ys ++ l))
            by (find_rewrite_lem app_ass; rewrite app_comm_cons; auto);
            clear H
      end.
      eapply RIR_handleMessage with (net0 := net') (p1 := p);
      simpl; repeat find_rewrite; eauto;
      simpl; repeat break_let; eauto; try find_inversion; eauto.
      intros. do_in_app. simpl in *.
      intuition; try find_apply_hyp_hyp; intuition; in_crush.
    - subst. simpl in *. subst. unfold exists_equivalent_network_with_aer.
      find_eapply_lem_hyp RIR_step_f; [|eapply SF_dup with (failed := [])]; eauto.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      match goal with
        | _ : raft_intermediate_reachable (mkN (?p :: _) _ ) |- _ =>
          (exists (mkN (ps' ++ [p]) st'))
      end.
      subst.
      (exists pli, plt, ci, n).
      simpl in *. intuition.
      + match goal with
          | _ : raft_intermediate_reachable (mkNetwork ?ps ?st) |- _ =>
            eapply RIR_handleMessage with (net0 := (mkNetwork ps st)) (p0 := p)
                                                                      (xs0 := (p :: xs))
        end; eauto;
        simpl in *; repeat find_rewrite; simpl in *; repeat break_let; eauto;
        repeat find_inversion; eauto.
        intros.
        do_in_app. simpl in *. intuition.
        find_apply_hyp_hyp. intuition; subst; auto.
      + f_equal. f_equal.
        destruct p; simpl in *; f_equal; intuition.
        subst.
        find_apply_lem_hyp handleAppendEntries_reply_spec; auto.
        intuition. subst. auto.
  Qed.

  Lemma append_entries_request_reply_correspondence_append_entries_reply :
    raft_net_invariant_append_entries_reply append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto; [|repeat find_rewrite; in_crush].
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli'.
      break_exists_name plt'.
      break_exists_name ci'.
      break_exists_name n'.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p0) (pSrc p0) (AppendEntries t0 n' pli' plt' es0 ci')]) st').
      subst.
      exists pli',plt',ci',n'. simpl in *; intuition.
      repeat find_rewrite.
      match goal with
        | H : nwPackets net' = (?xs ++ ?p :: ?ys) ++ ?l |- _ =>
          assert (nwPackets net' = xs ++ p :: (ys ++ l))
            by (find_rewrite_lem app_ass; rewrite app_comm_cons; auto);
            clear H
      end.
      eapply RIR_handleMessage with (net0 := net') (p1 := p);
      simpl; repeat find_rewrite; eauto;
      simpl; repeat break_let; eauto; try find_inversion; eauto.
      intros. do_in_app. simpl in *.
      intuition; try find_apply_hyp_hyp; intuition; in_crush.
    - do_in_map.
      subst. simpl in *.
      find_apply_lem_hyp handleAppendEntriesReply_packets.
      subst. simpl in *. intuition.
  Qed.


  Lemma append_entries_request_reply_correspondence_request_vote :
    raft_net_invariant_request_vote append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    - copy_eapply_prop_hyp pBody pBody; auto; [|repeat find_rewrite; in_crush].
      unfold exists_equivalent_network_with_aer in *.
      break_exists_name net'.
      break_exists_name pli'.
      break_exists_name plt'.
      break_exists_name ci'.
      break_exists_name n'.
      intuition.
      remember mkNetwork as mkN.
      remember mkPacket as mkP.
      unfold Net.name in *. simpl in *.
      exists (mkN (ps' ++ [mkP (pDst p0) (pSrc p0) (AppendEntries t0 n' pli' plt' es ci')]) st').
      subst.
      exists pli',plt',ci',n'. simpl in *; intuition.
      repeat find_rewrite.
      match goal with
        | H : nwPackets net' = (?xs ++ ?p :: ?ys) ++ ?l |- _ =>
          assert (nwPackets net' = xs ++ p :: (ys ++ l))
            by (find_rewrite_lem app_ass; rewrite app_comm_cons; auto);
            clear H
      end.
      eapply RIR_handleMessage with (net0 := net') (p1 := p);
      simpl; repeat find_rewrite; eauto;
      simpl; repeat break_let; eauto; try find_inversion; eauto.
      intros. do_in_app. simpl in *.
      intuition; try find_apply_hyp_hyp; intuition; in_crush.
    - subst. simpl in *. subst.
      unfold handleRequestVote in *.
      repeat break_match; find_inversion; congruence.
  Qed.

  Lemma append_entries_request_reply_correspondence_request_vote_reply :
    raft_net_invariant_request_vote_reply append_entries_request_reply_correspondence.
  Proof.
    red. unfold append_entries_request_reply_correspondence. intros.
    simpl in *.
    find_apply_hyp_hyp. intuition.
    copy_eapply_prop_hyp pBody pBody; auto; [|repeat find_rewrite; in_crush].
    unfold exists_equivalent_network_with_aer in *.
    break_exists_name net'.
    break_exists_name pli'.
    break_exists_name plt'.
    break_exists_name ci'.
    break_exists_name n'.
    intuition.
    remember mkNetwork as mkN.
    remember mkPacket as mkP.
    unfold Net.name in *. simpl in *.
    exists (mkN (ps' ++ [mkP (pDst p0) (pSrc p0) (AppendEntries t0 n' pli' plt' es ci')]) st').
    subst.
    exists pli',plt',ci',n'. simpl in *; intuition.
    repeat find_rewrite.
    match goal with
      | H : nwPackets net' = (?xs ++ ?p :: ?ys) ++ ?l |- _ =>
        assert (nwPackets net' = xs ++ p :: (ys ++ l))
          by (find_rewrite_lem app_ass; rewrite app_comm_cons; auto);
          clear H
    end.
    eapply RIR_handleMessage with (net0 := net') (p1 := p);
      simpl; repeat find_rewrite; eauto;
      simpl; repeat break_let; eauto; try find_inversion; eauto.
    intros. do_in_app. simpl in *.
    intuition; try find_apply_hyp_hyp; intuition; in_crush.
  Qed.

  Instance aerrci : append_entries_request_reply_correspondence_interface.
  split.
  intros. apply raft_net_invariant; auto.
  - exact append_entries_request_reply_correspondence_init.
  - exact append_entries_request_reply_correspondence_client_request.
  - exact append_entries_request_reply_correspondence_timeout.
  - exact append_entries_request_reply_correspondence_append_entries.
  - exact append_entries_request_reply_correspondence_append_entries_reply.
  - exact append_entries_request_reply_correspondence_request_vote.
  - exact append_entries_request_reply_correspondence_request_vote_reply.
  - exact append_entries_request_reply_correspondence_do_leader.
  - exact append_entries_request_reply_correspondence_do_generic_server.
  - exact append_entries_request_reply_correspondence_state_same_packet_subset.
  - exact append_entries_request_reply_correspondence_reboot.
  Qed.
  

End AppendEntriesRequestReplyCorrespondence.
