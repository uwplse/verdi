Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Sumbool.

Require Import Util.
Require Import Net.
Require Import GhostSimulations.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.

Require Import RaftRefinementInterface.

Section RaftRefinementProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Lemma refined_raft_invariant_handle_message P :
    forall xs p ys net st' ps' gd d l,
      refined_raft_net_invariant_append_entries P ->
      refined_raft_net_invariant_append_entries_reply P ->
      refined_raft_net_invariant_request_vote P ->
      refined_raft_net_invariant_request_vote_reply P ->
      handleMessage (pSrc p) (pDst p) (pBody p) (snd (nwState net (pDst p))) = (d, l) ->
      update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = gd ->
      P net ->
      refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage, update_elections_data_net in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop refined_raft_net_invariant_request_vote|
     eapply_prop refined_raft_net_invariant_request_vote_reply|
     eapply_prop refined_raft_net_invariant_append_entries|
     eapply_prop refined_raft_net_invariant_append_entries_reply]; eauto;
    unfold send_packets in *; simpl in *; intros; subst; auto; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma refined_raft_invariant_handle_input P :
    forall h inp net st' ps' gd out d l,
      refined_raft_net_invariant_timeout P ->
      refined_raft_net_invariant_client_request P ->
      handleInput h inp (snd (nwState net h)) = (out, d, l) ->
      update_elections_data_input h inp (nwState net h) = gd ->
      P net ->
      refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput, update_elections_data_input in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop refined_raft_net_invariant_timeout|
     eapply_prop refined_raft_net_invariant_client_request]; eauto; subst; auto.
  Qed.

  Theorem refined_raft_net_invariant :
    forall P net,
      refined_raft_net_invariant_init P ->
      refined_raft_net_invariant_client_request P ->
      refined_raft_net_invariant_timeout P ->
      refined_raft_net_invariant_append_entries P ->
      refined_raft_net_invariant_append_entries_reply P ->
      refined_raft_net_invariant_request_vote P ->
      refined_raft_net_invariant_request_vote_reply P ->
      refined_raft_net_invariant_do_leader P ->
      refined_raft_net_invariant_do_generic_server P ->
      refined_raft_net_invariant_state_same_packet_subset P ->
      refined_raft_net_invariant_reboot P ->
      refined_raft_intermediate_reachable net ->
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       + unfold refined_net_handlers in *. simpl in *.
         unfold RaftNetHandler, update_elections_data_net in *.
         repeat break_let.
         repeat find_inversion.
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2;
                nwState := update (nwState net) (pDst p)
                                  (update_elections_data_net (pDst p)
                                                             (pSrc p)
                                                             (pBody p)
                                                             (nwState net (pDst p)), r0) |})
           by (eapply RRIR_handleMessage; eauto; in_crush).
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := ((xs ++ ys)
                                ++ send_packets (pDst p) l2)
                               ++ send_packets (pDst p) l3 ;
            nwState := update
                         (nwState
                            {|
                              nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2;
                              nwState := update (nwState net)
                                                (pDst p)
                                                (update_elections_data_net
                                                   (pDst p) (pSrc p)
                                                   (pBody p) (nwState net (pDst p)), r0) |})
                         (pDst p)
                         (update_elections_data_net (pDst p)
                                                    (pSrc p) (pBody p) (nwState net (pDst p)), r1) |})
           by
             (eapply RRIR_doLeader; eauto;
              [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop refined_raft_net_invariant_do_generic_server. eauto.
         eapply_prop refined_raft_net_invariant_do_leader. eauto.
         eapply refined_raft_invariant_handle_message with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or. auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. in_crush.
       + unfold refined_input_handlers in *. simpl in *.
         unfold RaftInputHandler, update_elections_data_input in *. repeat break_let.
         repeat find_inversion.
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := nwPackets net ++ send_packets h l2;
                nwState := update (nwState net) h
                                  (update_elections_data_input h
                                                               inp
                                                               (nwState net h), r0) |})
           by (eapply RRIR_handleInput; eauto; in_crush).
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net
                                ++ send_packets h l2)
                               ++ send_packets h l4 ;
            nwState := update
                         (nwState
                            {|
                              nwPackets := nwPackets net ++ send_packets h l2;
                              nwState := update (nwState net)
                                                h
                                                (update_elections_data_input h inp
                                                                             (nwState net h), r0) |})
                         h
                         (update_elections_data_input h inp (nwState net h), r1) |})
           by
             (eapply RRIR_doLeader; eauto;
              [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop refined_raft_net_invariant_do_generic_server. eauto.
         eapply_prop refined_raft_net_invariant_do_leader. eauto.
         eapply refined_raft_invariant_handle_input with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or.
         auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. unfold send_packets.  intros. in_crush.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop refined_raft_net_invariant_reboot; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
         destruct (nwState net h); auto.
    - eapply refined_raft_invariant_handle_input; eauto.
    - eapply refined_raft_invariant_handle_message; eauto.
    - eapply_prop refined_raft_net_invariant_do_leader; eauto.
    - eapply_prop refined_raft_net_invariant_do_generic_server; eauto.
  Qed.

  Lemma refined_raft_invariant_handle_message' P :
    forall xs p ys net st' ps' gd d l,
      refined_raft_net_invariant_append_entries' P ->
      refined_raft_net_invariant_append_entries_reply' P ->
      refined_raft_net_invariant_request_vote' P ->
      refined_raft_net_invariant_request_vote_reply' P ->
      handleMessage (pSrc p) (pDst p) (pBody p) (snd (nwState net (pDst p))) = (d, l) ->
      update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = gd ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage, update_elections_data_net in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop refined_raft_net_invariant_request_vote'|
     eapply_prop refined_raft_net_invariant_request_vote_reply'|
     eapply_prop refined_raft_net_invariant_append_entries'|
     eapply_prop refined_raft_net_invariant_append_entries_reply']; eauto;
    unfold send_packets in *; simpl in *; intros; subst; auto; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma refined_raft_invariant_handle_input' P :
    forall h inp net st' ps' gd out d l,
      refined_raft_net_invariant_timeout' P ->
      refined_raft_net_invariant_client_request' P ->
      handleInput h inp (snd (nwState net h)) = (out, d, l) ->
      update_elections_data_input h inp (nwState net h) = gd ->
      P net ->
      refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput, update_elections_data_input in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop refined_raft_net_invariant_timeout'|
     eapply_prop refined_raft_net_invariant_client_request']; eauto; subst; auto.
  Qed.

  Theorem refined_raft_net_invariant' :
    forall P net,
      refined_raft_net_invariant_init P ->
      refined_raft_net_invariant_client_request' P ->
      refined_raft_net_invariant_timeout' P ->
      refined_raft_net_invariant_append_entries' P ->
      refined_raft_net_invariant_append_entries_reply' P ->
      refined_raft_net_invariant_request_vote' P ->
      refined_raft_net_invariant_request_vote_reply' P ->
      refined_raft_net_invariant_do_leader' P ->
      refined_raft_net_invariant_do_generic_server' P ->
      refined_raft_net_invariant_state_same_packet_subset P ->
      refined_raft_net_invariant_reboot' P ->
      refined_raft_intermediate_reachable net ->
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       + match goal with 
         | [ H : refined_raft_intermediate_reachable _ |- _ ?x ] => 
           assert (refined_raft_intermediate_reachable x) as Hpost
                  by (eapply RRIR_step_f; eauto; eapply SF_deliver; eauto)
         
         end.
         unfold refined_net_handlers in *. simpl in *.
         unfold RaftNetHandler, update_elections_data_net in *.
         repeat break_let.
         repeat find_inversion.
         match goal with 
         | [ H : refined_raft_intermediate_reachable ?net, H' : context [net]  |- _ ] => 
           match type of H' with
           | refined_raft_intermediate_reachable _ => move H after H'
           end
         end.
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2;
                nwState := update (nwState net) (pDst p)
                                  (update_elections_data_net (pDst p)
                                                             (pSrc p)
                                                             (pBody p)
                                                             (nwState net (pDst p)), r0) |})
           by (eapply RRIR_handleMessage; eauto; in_crush).
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := ((xs ++ ys)
                                ++ send_packets (pDst p) l2)
                               ++ send_packets (pDst p) l3 ;
            nwState := update
                         (nwState
                            {|
                              nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2;
                              nwState := update (nwState net)
                                                (pDst p)
                                                (update_elections_data_net
                                                   (pDst p) (pSrc p)
                                                   (pBody p) (nwState net (pDst p)), r0) |})
                         (pDst p)
                         (update_elections_data_net (pDst p)
                                                    (pSrc p) (pBody p) (nwState net (pDst p)), r1) |})
           by
             (eapply RRIR_doLeader; eauto;
              [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop refined_raft_net_invariant_do_generic_server'. eauto.
         eapply_prop refined_raft_net_invariant_do_leader'. eauto.
         eapply refined_raft_invariant_handle_message' with (P := P); auto.
         eauto. eauto.   auto. eauto.  eauto. eauto using in_app_or. auto.
         eauto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or. auto. auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. in_crush.
       + match goal with 
         | [ H : refined_raft_intermediate_reachable _ |- _ ?x ] => 
           assert (refined_raft_intermediate_reachable x) as Hpost
               by (eapply RRIR_step_f; eauto; eapply SF_input; eauto)
         end.
         unfold refined_input_handlers in *. simpl in *.
         unfold RaftInputHandler, update_elections_data_input in *. repeat break_let.
         repeat find_inversion.
         match goal with 
         | [ H : refined_raft_intermediate_reachable ?net, H' : context [net]  |- _ ] => 
           match type of H' with
           | refined_raft_intermediate_reachable _ => move H after H'
           end
         end.                    

         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := nwPackets net ++ send_packets h l2;
                nwState := update (nwState net) h
                                  (update_elections_data_input h
                                                               inp
                                                               (nwState net h), r0) |})
           by (eapply RRIR_handleInput; eauto; in_crush).
         assert
           (refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net
                                ++ send_packets h l2)
                               ++ send_packets h l4 ;
            nwState := update
                         (nwState
                            {|
                              nwPackets := nwPackets net ++ send_packets h l2;
                              nwState := update (nwState net)
                                                h
                                                (update_elections_data_input h inp
                                                                             (nwState net h), r0) |})
                         h
                         (update_elections_data_input h inp (nwState net h), r1) |})
           by
             (eapply RRIR_doLeader; eauto;
              [simpl in *; break_if; try congruence; eauto| in_crush]).
         eapply_prop refined_raft_net_invariant_do_generic_server'. eauto.
         eapply_prop refined_raft_net_invariant_do_leader'. eauto.
         eapply refined_raft_invariant_handle_input' with (P := P); auto. 
         eauto. all:auto. all: eauto. eauto using in_app_or. 
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or.
         auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. unfold send_packets.  intros. in_crush.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop refined_raft_net_invariant_reboot'; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
         * econstructor. eauto. eapply SF_reboot; eauto.
         * destruct (nwState net h); auto.
    - eapply refined_raft_invariant_handle_input'; eauto.
      eapply RRIR_handleInput; eauto.
    - eapply refined_raft_invariant_handle_message'; eauto.
      eapply RRIR_handleMessage; eauto.
    - eapply_prop refined_raft_net_invariant_do_leader'; eauto.
      eapply RRIR_doLeader; eauto.
    - eapply_prop refined_raft_net_invariant_do_generic_server'; eauto.
      eapply RRIR_doGenericServer; eauto.
  Qed.

  Require Import FunctionalExtensionality.

  Ltac workhorse :=
    try match goal with
        | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal
      end;
    try match goal with
        | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros
      end;
      repeat break_match;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => invc H
             end;
      repeat (simpl in *; subst);
      repeat rewrite map_app;
      repeat rewrite map_map.


  Theorem simulation_1 :
    forall net,
      refined_raft_intermediate_reachable net ->
      raft_intermediate_reachable (deghost net).
  Proof.
    intros.
    induction H.
    - constructor.
    - simpl in *.
      pose proof (RIR_step_f).
      specialize (H1 failed (deghost net) failed' (deghost net') out).
      apply H1; auto.
      apply ghost_simulation_1; auto.
    - unfold deghost in *. simpl in *.
      eapply RIR_handleInput; eauto.
      + simpl in *. repeat break_match. simpl in *.
        assert (nwState h = (g, d0)) by eauto.
        repeat find_rewrite. eauto.
      + intros. simpl in *.
        repeat break_match; subst; simpl in *;
        repeat find_higher_order_rewrite; break_if; subst; simpl in *;
        congruence.
      + intros. simpl in *. in_crush.
        find_apply_hyp_hyp.
        in_crush.
    - unfold deghost in *. simpl in *.
      pose proof (RIR_handleMessage).
      specialize
        (H5 (@mkPacket _ multi_params
                       (pSrc p)
                       (pDst p)
                       (pBody p))).
      eapply H5; eauto.
      + simpl in *. repeat break_match. simpl in *.
        repeat find_rewrite. eauto.
      + simpl in *.
        unfold raft_refined_base_params, raft_refined_multi_params in *.
        simpl in *.
        repeat find_rewrite.
        map_crush. eauto.
      + intros. repeat break_match. simpl in *.
        repeat find_higher_order_rewrite.
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
    - unfold deghost in *. simpl in *.
      eapply RIR_doLeader; eauto.
      + simpl in *. repeat break_match. simpl in *.
        assert (nwState h = (g, d0)) by eauto.
        repeat find_rewrite. repeat find_inversion. eauto.
      + simpl in *.
        intros. repeat break_match; simpl in *;
        repeat find_higher_order_rewrite;
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
    - unfold deghost in *. simpl in *.
      eapply RIR_doGenericServer; eauto.
      + simpl in *. repeat break_match. simpl in *.
        assert (nwState h = (g, d0)) by eauto.
        repeat find_rewrite. repeat find_inversion. eauto.
      + simpl in *.
        intros. repeat break_match; simpl in *;
        repeat find_higher_order_rewrite;
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
  Qed.

  Theorem lift_prop :
    forall P,
      (forall net, raft_intermediate_reachable net -> P net) ->
      (forall net, refined_raft_intermediate_reachable net -> P (deghost net)).
  Proof.
    intros.
    eauto using simulation_1.
  Qed.

  Require Import FunctionalExtensionality.

  Theorem simulation_2 :
    forall net,
      raft_intermediate_reachable net ->
      exists rnet,
        net = deghost rnet /\
        refined_raft_intermediate_reachable rnet.
  Proof.
    intros.
    induction H.
    - exists (reghost step_m_init). intuition.
        unfold reghost. constructor.
    - break_exists. break_and.
      apply ghost_simulation_2 with (gnet := x) in H0; auto.
      repeat (break_exists; intuition).
      subst.
      exists x0. intuition.
      eapply RRIR_step_f; eauto.
    - break_exists. break_and.
      subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) h (update_elections_data_input h inp (nwState x h), d)
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *.
        eapply RRIR_handleInput; repeat break_match; simpl in *; eauto.
        simpl in *. in_crush.
        find_apply_hyp_hyp. in_crush.
        destruct x. auto.
    - break_exists. break_and.
      subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) (pDst p)
                             (update_elections_data_net (pDst p) (pSrc p)
                                                 (pBody p) (nwState x (pDst p)), d)
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *.
        eapply RRIR_handleMessage with (p0 := ghost_packet p);
          repeat break_match; simpl in *; eauto.
        * simpl in *.
          match goal with
        | H : map _ ?la = ?lb |- _ =>
          symmetry in H;
            pose proof @map_inverses _ _ la lb deghost_packet ghost_packet
          end.
          repeat (forwards; [intro a; destruct a; reflexivity|]; concludes;
                  match goal with
                    | H :  forall _ : packet,  _ = _ |- _ => clear H
                  end).
          concludes. map_crush. eauto.
        * simpl in *. in_crush.
          find_apply_hyp_hyp. in_crush.
    - break_exists. break_and. subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) h (fst (nwState x h) , d')
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *. simpl in *. repeat break_match; simpl in *.
        eapply RRIR_doLeader with (d0 := d) (h0 := h);
          repeat (break_match; simpl in *); eauto.
        * simpl in *. find_rewrite. simpl in *. auto.
        * simpl in *. in_crush.
          find_apply_hyp_hyp. in_crush.
          destruct x. auto.
    - break_exists. break_and. subst.
      exists {| nwPackets := map ghost_packet ps' ;
           nwState := update (nwState x) h (fst (nwState x h) , d')
        |}. intuition.
      + unfold deghost. simpl in *. map_crush. f_equal.
        * map_id.
        * apply functional_extensionality.
          intros. find_higher_order_rewrite.
          repeat break_match; auto. simpl in *. congruence.
      + unfold deghost in *. simpl in *. repeat break_match; simpl in *.
        eapply RRIR_doGenericServer with (d0 := d) (h0 := h);
          repeat (break_match; simpl in *); eauto.
        * simpl in *. find_rewrite. simpl in *. auto.
        * simpl in *. in_crush.
          find_apply_hyp_hyp. in_crush.
          destruct x. auto.
  Qed.

  Theorem lower_prop :
    forall P : _ -> Prop,
      (forall net, refined_raft_intermediate_reachable net -> P (deghost net)) ->
      (forall net, raft_intermediate_reachable net -> P net).
  Proof.
    intros.
    find_apply_lem_hyp simulation_2.
    break_exists. intuition. subst. eauto.
  Qed.

  Lemma deghost_spec :
    forall (net : @network _ raft_refined_multi_params) h,
      nwState (deghost net) h = snd (nwState net h).
  Proof.
    intros.
    destruct net; auto.
  Qed.

  Instance rri : raft_refinement_interface.
  Proof.
    split.
    - exact refined_raft_net_invariant.
    - exact refined_raft_net_invariant'.
    - exact lift_prop.
    - exact lower_prop.
    - exact deghost_spec.
    - exact simulation_1.
  Qed.
End RaftRefinementProof.

Hint Extern 4 (@BaseParams) => apply raft_refined_base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply raft_refined_multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply raft_refined_failure_params : typeclass_instances.
