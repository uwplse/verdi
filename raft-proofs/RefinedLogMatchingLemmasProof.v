Require Import GhostSimulations.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import LogMatchingInterface.
Require Import SortedInterface.
Require Import AllEntriesIndicesGt0Interface.

Require Import RefinedLogMatchingLemmasInterface.

Section RefinedLogMatchingLemmas.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lmi : log_matching_interface}.
  Context {si : sorted_interface}.
  Context {aeigt0 : allEntries_indices_gt_0_interface}.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof.
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Ltac forward_invariant :=
    match goal with
    | [ H : refined_raft_intermediate_reachable _, H' : _ |- _ ] =>
      apply H' in H; clear H'
    end.

  Ltac forward_nw_invariant :=
    match goal with
    | [ H : forall _ _ _ _ _ _ _, In _ _ -> pBody _ = _ -> _,
        H' : In _ _,
        H'' : pBody _ = _ |- _ ] =>
      specialize (H _ _ _ _ _ _ _ H' H'')
    end.


  Lemma entries_contiguous_nw_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_contiguous_nw net.
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_nw, entries_contiguous_nw in *. intuition.
    find_apply_lem_hyp ghost_packet.
    forward_nw_invariant. red. intuition.
  Qed.

  Lemma entries_gt_0_nw_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_gt_0_nw net.
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_nw, entries_gt_0_nw in *. intuition.
    find_apply_lem_hyp ghost_packet.
    forward_nw_invariant. break_and.
    find_apply_hyp_hyp. omega.
  Qed.

  Lemma entries_sorted_nw_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_sorted_nw net.
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    forward_invariant.
    unfold log_matching, log_matching_nw, entries_sorted_nw in *. intuition.
    find_apply_lem_hyp ghost_packet.
    unfold logs_sorted in *. break_and.
    unfold logs_sorted_nw in *.
    eauto.
  Qed.

  Lemma entries_gt_0_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_gt_0 net.
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_hosts, entries_gt_0 in *. intuition.
    match goal with
    | [ H : _ |- _ ] => setoid_rewrite deghost_spec in H
    end.
    eauto.
  Qed.

  Lemma entries_contiguous_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_contiguous net.
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_hosts, entries_contiguous in *. break_and.
    intros.
    repeat match goal with
    | [ H : _ |- _ ] => setoid_rewrite deghost_spec in H
    end.
    red. intuition eauto.
    find_apply_hyp_hyp. auto.
  Qed.

  Lemma entries_sorted_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_sorted net.
  Proof.
    intros.
    pose proof (lift_prop _ logs_sorted_invariant).
    forward_invariant.
    unfold entries_sorted, logs_sorted, logs_sorted_host in *. break_and.
    match goal with
    | [ H : _ |- _ ] => setoid_rewrite deghost_spec in H
    end.
    eauto.
  Qed.

  Lemma entries_match_invariant :
    forall net h h',
      refined_raft_intermediate_reachable net ->
      entries_match (log (snd (nwState net h))) (log (snd (nwState net h'))).
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_hosts in *. break_and.
    repeat match goal with
    | [ H : _ |- _ ] => setoid_rewrite deghost_spec in H
    end.
    eauto.
  Qed.

  Lemma entries_match_nw_1_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_match_nw_1 net.
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_nw, entries_match_nw_1 in *. break_and.
    intros.
    repeat find_apply_lem_hyp ghost_packet.
    match goal with
    | [ H : forall _ _ _ _ _ _ , _,
        Hp : In (deghost_packet ?p) _,
        Hp' : In (deghost_packet ?p') _,
        Hes : pBody ?p = AppendEntries _ _ _ _ ?es _,
        Hes' : pBody ?p' = AppendEntries _ _ _ _ ?es' _,
        He'' : In ?e'' ?es
        |- In ?e'' ?es' ] =>
      specialize (H _ _ _ _ _ _ _ Hp Hes); break_and;
      match goal with
      | [ H' : forall _ _ _ _ _ _ , _ |- _ ] =>
        specialize (H' _ _ _ _ _ _ _ Hp' Hes')
      end
    end.

    match goal with
    | [ H : forall _ _, In _ _ -> _ |- _ ] => eapply H with (e1 := e) (e2 := e'); auto
    end.
  Qed.

  Lemma entries_match_nw_host_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      entries_match_nw_host net.
  Proof.
    intros.
    pose proof (lift_prop _ log_matching_invariant).
    forward_invariant.
    unfold log_matching, log_matching_nw, entries_match_nw_host in *. break_and.
    intros.
    repeat find_apply_lem_hyp ghost_packet.
    forward_nw_invariant. break_and.
    match goal with
    | [  |- context [ snd (nwState ?net ?h) ] ] =>
      replace (snd (nwState net h)) with (nwState (deghost net) h) in * by auto using deghost_spec
    end.
    match goal with
    | [ H : forall _ _ _, In _ ?es -> _,
        He : In ?e ?es,
        He' : In ?e' ?log,
        Hle : eIndex ?e'' <= eIndex ?e
        |- In ?e'' ?log ] =>
      specialize (H _ _ _ He He')
    end.
    repeat concludes; break_and. eauto.
  Qed.

  Lemma allEntries_gt_0_invariant :
    forall net h e,
      refined_raft_intermediate_reachable net ->
      In e (map snd (allEntries (fst (nwState net h)))) ->
      eIndex e > 0.
  Proof.
    intros.
    eapply allEntries_indices_gt_0_invariant; eauto.
  Qed.

  Instance rlmli : refined_log_matching_lemmas_interface.
  Proof.
    constructor.
    - apply entries_contiguous_nw_invariant.
    - apply entries_gt_0_nw_invariant.
    - apply entries_sorted_nw_invariant.
    - apply entries_gt_0_invariant.
    - apply entries_contiguous_invariant.
    - apply entries_sorted_invariant.
    - apply entries_match_invariant.
    - apply entries_match_nw_1_invariant.
    - apply entries_match_nw_host_invariant.
    - apply allEntries_gt_0_invariant.
  Qed.
End RefinedLogMatchingLemmas.
