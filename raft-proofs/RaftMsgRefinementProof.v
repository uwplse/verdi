Require Import NPeano.
Require Import Sumbool.
Require Import FunctionalExtensionality.

Require Import GhostSimulations.
Require Import RaftState.
Require Import Raft.
Require Import SpecLemmas.

Require Import RaftRefinementInterface.
Require Import RaftMsgRefinementInterface.

Section RaftMsgRefinement.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Lemma msg_refined_raft_invariant_handle_message P :
    forall xs p ys net st' ps' gd d l,
      msg_refined_raft_net_invariant_append_entries P ->
      msg_refined_raft_net_invariant_append_entries_reply P ->
      msg_refined_raft_net_invariant_request_vote P ->
      msg_refined_raft_net_invariant_request_vote_reply P ->
      handleMessage (pSrc p) (pDst p) (snd (pBody p)) (snd (nwState net (pDst p))) = (d, l) ->
      update_elections_data_net (pDst p) (pSrc p) (snd (pBody p)) (nwState net (pDst p)) = gd ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) (@add_ghost_msg _ _ _ ghost_log_params (pDst p) (gd, d) l))) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage, update_elections_data_net in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop msg_refined_raft_net_invariant_request_vote|
     eapply_prop msg_refined_raft_net_invariant_request_vote_reply|
     eapply_prop msg_refined_raft_net_invariant_append_entries|
     eapply_prop msg_refined_raft_net_invariant_append_entries_reply]; eauto;
    unfold send_packets in *; simpl in *; intros; subst; auto; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma msg_refined_raft_invariant_handle_input P :
    forall h inp net st' ps' gd out d l,
      msg_refined_raft_net_invariant_timeout P ->
      msg_refined_raft_net_invariant_client_request P ->
      handleInput h inp (snd (nwState net h)) = (out, d, l) ->
      update_elections_data_input h inp (nwState net h) = gd ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h (@add_ghost_msg _ _ _ ghost_log_params h (gd, d) l))) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput, update_elections_data_input in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop msg_refined_raft_net_invariant_timeout|
     eapply_prop msg_refined_raft_net_invariant_client_request]; eauto; subst; auto.
  Qed.

  Theorem msg_refined_raft_net_invariant :
    forall P net,
      msg_refined_raft_net_invariant_init P ->
      msg_refined_raft_net_invariant_client_request P ->
      msg_refined_raft_net_invariant_timeout P ->
      msg_refined_raft_net_invariant_append_entries P ->
      msg_refined_raft_net_invariant_append_entries_reply P ->
      msg_refined_raft_net_invariant_request_vote P ->
      msg_refined_raft_net_invariant_request_vote_reply P ->
      msg_refined_raft_net_invariant_do_leader P ->
      msg_refined_raft_net_invariant_do_generic_server P ->
      msg_refined_raft_net_invariant_state_same_packet_subset P ->
      msg_refined_raft_net_invariant_reboot P ->
      msg_refined_raft_intermediate_reachable net ->
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       
       + unfold mgv_refined_net_handlers in *. simpl in *.
         unfold refined_net_handlers in *. simpl in *.
         unfold RaftNetHandler in *.
         repeat break_let.
         repeat find_inversion.
         remember (update_elections_data_net (pDst p) (pSrc p) (snd (pBody p))
                                             (nwState net (pDst p))) as post_ghost_state.
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++ send_packets (pDst p)
                                       (@add_ghost_msg _ _ _ ghost_log_params (pDst p)
                                                       (post_ghost_state, r0) l4);
                nwState := update (nwState net) (pDst p)
                                  (post_ghost_state, r0) |})
           by (subst; eapply MRRIR_handleMessage; eauto; in_crush).
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++
                                       send_packets (pDst p)
                                       (@add_ghost_msg _ _ _ ghost_log_params (pDst p)
                                                       (post_ghost_state, r0) l4)
                                       ++
                                       send_packets (pDst p)
                                       (@add_ghost_msg _ _ _ ghost_log_params (pDst p)
                                                       (post_ghost_state, r1) l5);
                nwState := update (nwState net) (pDst p)
                                  (post_ghost_state, r1) |}) by
             (eapply MRRIR_doLeader; eauto;
              try solve [in_crush];
              simpl in *; intros; repeat break_if; try congruence; auto).
         subst.
         eapply_prop msg_refined_raft_net_invariant_do_generic_server. eauto.
         eapply_prop msg_refined_raft_net_invariant_do_leader. eauto.
         eapply msg_refined_raft_invariant_handle_message with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or.
         simpl.
         {
           match goal with
             | H : msg_refined_raft_intermediate_reachable ?net |-
               msg_refined_raft_intermediate_reachable ?net' =>
               assert (net = net')
           end.
           simpl.
           f_equal; auto.
           - repeat rewrite app_ass. auto.
           - apply functional_extensionality.
             intros. repeat break_if; simpl; auto.
           - repeat find_rewrite; auto.
         }
         simpl in *. break_if; eauto; congruence.
         simpl in *.
         intros. repeat break_if; auto.
         intros. simpl in *.
         in_crush. 
         unfold add_ghost_msg in *. do_in_map.
         subst. do_in_app. intuition; try do_in_app; intuition.
         * left. apply in_app_iff. left. apply in_app_iff. right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * left. apply in_app_iff. right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           
       + unfold mgv_refined_input_handlers in *. simpl in *.
         unfold refined_input_handlers in *. simpl in *.
         unfold RaftInputHandler in *.
         repeat break_let.
         repeat find_inversion.
         remember (update_elections_data_input h inp
                                               (nwState net h))
           as post_ghost_state.
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net) ++ send_packets h
                                       (@add_ghost_msg _ _ _ ghost_log_params h
                                                       (post_ghost_state, r0) l4);
                nwState := update (nwState net) h
                                  (post_ghost_state, r0) |})
           by (subst; eapply MRRIR_handleInput; eauto; in_crush).
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net) ++
                                       send_packets h
                                       (@add_ghost_msg _ _ _ ghost_log_params h
                                                       (post_ghost_state, r0) l4)
                                       ++
                                       send_packets h
                                       (@add_ghost_msg _ _ _ ghost_log_params h
                                                       (post_ghost_state, r1) l6);
                nwState := update (nwState net) h
                                  (post_ghost_state, r1) |}) by
             (eapply MRRIR_doLeader; eauto;
              try solve [in_crush];
              simpl in *; intros; repeat break_if; try congruence; auto).
         subst.
         eapply_prop msg_refined_raft_net_invariant_do_generic_server. eauto.
         eapply_prop msg_refined_raft_net_invariant_do_leader. eauto.
         eapply msg_refined_raft_invariant_handle_input with (P := P); eauto using in_app_or.
         auto.
         simpl. break_if; intuition eauto.
         eauto.
         simpl. eapply in_app_or.
         simpl.
         {
           match goal with
             | H : msg_refined_raft_intermediate_reachable ?net |-
               msg_refined_raft_intermediate_reachable ?net' =>
               assert (net = net')
           end.
           simpl.
           f_equal; auto.
           - repeat rewrite app_ass. auto.
           - apply functional_extensionality.
             intros. repeat break_if; simpl; auto.
           - repeat find_rewrite; auto.
         }
         simpl in *. break_if; eauto; congruence.
         simpl in *.
         intros. repeat break_if; auto.
         intros. simpl in *.
         in_crush. 
         unfold add_ghost_msg in *. do_in_map.
         subst. do_in_app. intuition; try do_in_app; intuition.
         * left. apply in_app_iff. left. apply in_app_iff. right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * left. apply in_app_iff. right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop msg_refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop msg_refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop msg_refined_raft_net_invariant_reboot; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
         destruct (nwState net h); auto.
    - eapply msg_refined_raft_invariant_handle_input; eauto.
    - eapply msg_refined_raft_invariant_handle_message; eauto.
    - eapply_prop msg_refined_raft_net_invariant_do_leader; eauto.
    - eapply_prop msg_refined_raft_net_invariant_do_generic_server; eauto.
  Qed.

  Lemma msg_refined_raft_invariant_handle_message' P :
    forall xs p ys net st' ps' gd d l,
      msg_refined_raft_net_invariant_append_entries' P ->
      msg_refined_raft_net_invariant_append_entries_reply' P ->
      msg_refined_raft_net_invariant_request_vote' P ->
      msg_refined_raft_net_invariant_request_vote_reply' P ->
      handleMessage (pSrc p) (pDst p) (snd (pBody p)) (snd (nwState net (pDst p))) = (d, l) ->
      update_elections_data_net (pDst p) (pSrc p) (snd (pBody p)) (nwState net (pDst p)) = gd ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) (@add_ghost_msg _ _ _ ghost_log_params (pDst p) (gd, d) l))) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage, update_elections_data_net in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop msg_refined_raft_net_invariant_request_vote'|
     eapply_prop msg_refined_raft_net_invariant_request_vote_reply'|
     eapply_prop msg_refined_raft_net_invariant_append_entries'|
     eapply_prop msg_refined_raft_net_invariant_append_entries_reply']; eauto;
    unfold send_packets in *; simpl in *; intros; subst; auto; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma msg_refined_raft_invariant_handle_input' P :
    forall h inp net st' ps' gd out d l,
      msg_refined_raft_net_invariant_timeout' P ->
      msg_refined_raft_net_invariant_client_request' P ->
      handleInput h inp (snd (nwState net h)) = (out, d, l) ->
      update_elections_data_input h inp (nwState net h) = gd ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h (@add_ghost_msg _ _ _ ghost_log_params h (gd, d) l))) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput, update_elections_data_input in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop msg_refined_raft_net_invariant_timeout'|
     eapply_prop msg_refined_raft_net_invariant_client_request']; eauto; subst; auto.
  Qed.

  Theorem msg_refined_raft_net_invariant' :
    forall P net,
      msg_refined_raft_net_invariant_init P ->
      msg_refined_raft_net_invariant_client_request' P ->
      msg_refined_raft_net_invariant_timeout' P ->
      msg_refined_raft_net_invariant_append_entries' P ->
      msg_refined_raft_net_invariant_append_entries_reply' P ->
      msg_refined_raft_net_invariant_request_vote' P ->
      msg_refined_raft_net_invariant_request_vote_reply' P ->
      msg_refined_raft_net_invariant_do_leader' P ->
      msg_refined_raft_net_invariant_do_generic_server' P ->
      msg_refined_raft_net_invariant_state_same_packet_subset' P ->
      msg_refined_raft_net_invariant_reboot' P ->
      msg_refined_raft_intermediate_reachable net ->
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       + match goal with 
         | [ H : msg_refined_raft_intermediate_reachable _ |- _ ?x ] => 
           assert (msg_refined_raft_intermediate_reachable x) as Hpost
                  by (eapply MRRIR_step_f; eauto; eapply SF_deliver; eauto)
         
         end.
         unfold mgv_refined_net_handlers in *. simpl in *.
         unfold refined_net_handlers in *. simpl in *.
         unfold RaftNetHandler, update_elections_data_net in *.
         repeat break_let.
         repeat find_inversion.
         match goal with 
         | [ H : msg_refined_raft_intermediate_reachable ?net, H' : context [net]  |- _ ] => 
           match type of H' with
           | msg_refined_raft_intermediate_reachable _ => move H after H'
           end
         end.
         remember (update_elections_data_net (pDst p) (pSrc p) (snd (pBody p))
                                             (nwState net (pDst p))) as post_ghost_state.
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++ send_packets (pDst p)
                                       (@add_ghost_msg _ _ _ ghost_log_params (pDst p)
                                                       (post_ghost_state, r0) l4);
                nwState := update (nwState net) (pDst p)
                                  (post_ghost_state, r0) |})
           by (subst; eapply MRRIR_handleMessage; eauto; in_crush).
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (xs ++ ys) ++
                                       send_packets (pDst p)
                                       (@add_ghost_msg _ _ _ ghost_log_params (pDst p)
                                                       (post_ghost_state, r0) l4)
                                       ++
                                       send_packets (pDst p)
                                       (@add_ghost_msg _ _ _ ghost_log_params (pDst p)
                                                       (post_ghost_state, r1) l5);
                nwState := update (nwState net) (pDst p)
                                  (post_ghost_state, r1) |}) by
             (eapply MRRIR_doLeader; eauto;
              try solve [in_crush];
              simpl in *; intros; repeat break_if; try congruence; auto).
         subst.
         eapply_prop msg_refined_raft_net_invariant_do_generic_server'. eauto.
         eapply_prop msg_refined_raft_net_invariant_do_leader'. eauto.
         eapply msg_refined_raft_invariant_handle_message' with (P := P); auto.
         eauto. eauto.   auto. eauto.  eauto. eauto using in_app_or. auto.
         eauto.
         simpl. break_if; intuition eauto.
         simpl. intros. break_if; intuition eauto.
         simpl. in_crush. auto. auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. in_crush.
         (* here *)
         unfold add_ghost_msg in *. do_in_map.
         subst. do_in_app. intuition; try do_in_app; intuition.
         * left. apply in_app_iff. right. apply in_app_iff. left.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * left. apply in_app_iff. right.
           apply in_app_iff. right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
       + match goal with 
         | [ H : msg_refined_raft_intermediate_reachable _ |- _ ?x ] => 
           assert (msg_refined_raft_intermediate_reachable x) as Hpost
                  by (eapply MRRIR_step_f; eauto; eapply SF_input; eauto)
         
         end.
         unfold mgv_refined_input_handlers in *. simpl in *.
         unfold refined_input_handlers in *. simpl in *.
         unfold RaftInputHandler, update_elections_data_input in *.
         repeat break_let.
         repeat find_inversion.
         match goal with 
         | [ H : msg_refined_raft_intermediate_reachable ?net, H' : context [net]  |- _ ] => 
           match type of H' with
           | msg_refined_raft_intermediate_reachable _ => move H after H'
           end
         end.
         remember (update_elections_data_input h inp
                                               (nwState net h))
           as post_ghost_state.
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net) ++ send_packets h
                                       (@add_ghost_msg _ _ _ ghost_log_params h
                                                       (post_ghost_state, r0) l4);
                nwState := update (nwState net) h
                                  (post_ghost_state, r0) |})
           by (subst; eapply MRRIR_handleInput; eauto; in_crush).
         assert
           (msg_refined_raft_intermediate_reachable
              {|
                nwPackets := (nwPackets net) ++
                                       send_packets h
                                       (@add_ghost_msg _ _ _ ghost_log_params h
                                                       (post_ghost_state, r0) l4)
                                       ++
                                       send_packets h
                                       (@add_ghost_msg _ _ _ ghost_log_params h
                                                       (post_ghost_state, r1) l6);
                nwState := update (nwState net) h
                                  (post_ghost_state, r1) |}) by
             (eapply MRRIR_doLeader; eauto;
              try solve [in_crush];
              simpl in *; intros; repeat break_if; try congruence; auto).
         subst.
         eapply_prop msg_refined_raft_net_invariant_do_generic_server'. eauto.
         eapply_prop msg_refined_raft_net_invariant_do_leader'. eauto.
         eapply msg_refined_raft_invariant_handle_input' with (P := P); auto.
         eauto. eauto.   auto. eauto.  eauto. eauto using in_app_or. auto.
         eauto.
         simpl. break_if; intuition eauto.
         simpl. intros. break_if; intuition eauto.
         simpl. in_crush. auto. auto.
         simpl. break_if; eauto; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl. in_crush.
         unfold add_ghost_msg in *. do_in_map.
         subst. do_in_app. intuition; try do_in_app; intuition.
         * left. apply in_app_iff. right. apply in_app_iff. left.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * left. apply in_app_iff. right.
           apply in_app_iff. right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
           simpl in *. f_equal. f_equal.
           unfold write_ghost_log. simpl.
           find_apply_lem_hyp doGenericServer_log.
           find_apply_lem_hyp doLeader_log.
           repeat find_rewrite. auto.
         * right.
           simpl in *.
           rewrite map_map.
           apply in_map_iff.
           eexists; intuition; eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop msg_refined_raft_net_invariant_state_same_packet_subset'; [|eauto|idtac|]; eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end.
         eapply_prop msg_refined_raft_net_invariant_state_same_packet_subset'; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop msg_refined_raft_net_invariant_reboot'; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
         * econstructor. eauto. eapply SF_reboot; eauto.
         * destruct (nwState net h); auto.
    - eapply msg_refined_raft_invariant_handle_input'; eauto.
      eapply MRRIR_handleInput; eauto.
    - eapply msg_refined_raft_invariant_handle_message'; eauto.
      eapply MRRIR_handleMessage; eauto.
    - eapply_prop msg_refined_raft_net_invariant_do_leader'; eauto.
      eapply MRRIR_doLeader; eauto.
    - eapply_prop msg_refined_raft_net_invariant_do_generic_server'; eauto.
      eapply MRRIR_doGenericServer; eauto.
  Qed.

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


  Notation mgv_deghost := (@mgv_deghost _ _ _ ghost_log_params).
  
  Theorem simulation_1 :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      refined_raft_intermediate_reachable (mgv_deghost net).
  Proof.
    intros.
    induction H.
    - constructor.
    - simpl in *.
      pose proof (RRIR_step_f).
      specialize (H1 failed (mgv_deghost net) failed' (mgv_deghost net') out).
      apply H1; auto.
      apply (@mgv_ghost_simulation_1 _ _ _ ghost_log_params); auto.
    - unfold mgv_deghost in *. simpl in *.
      eapply RRIR_handleInput; eauto.
      + simpl in *. repeat break_match. simpl in *. eauto.
      + intros. simpl in *.
        repeat break_match; subst; simpl in *;
        repeat find_higher_order_rewrite; break_if; subst; simpl in *;
        congruence.
      + intros. simpl in *. in_crush.
        find_apply_hyp_hyp.
        in_crush.
        right.
        unfold add_ghost_msg in *.
        do_in_map. subst. simpl in *.
        apply in_map_iff. eauto.
    - unfold mgv_deghost in *. simpl in *.
      pose proof (RRIR_handleMessage).
      specialize
        (H5 (@mkPacket _ raft_refined_multi_params
                       (pSrc p)
                       (pDst p)
                       (snd (pBody p)))).
      eapply H5; eauto.
      + simpl in *. repeat break_match. simpl in *.
        repeat find_rewrite. eauto.
      + simpl in *.
        unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params, raft_msg_refined_multi_params, raft_refined_multi_params in *.
        simpl in *.
        unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params, raft_msg_refined_multi_params, raft_refined_multi_params in *.
        simpl in *. repeat find_rewrite.
        map_crush. eauto.
      + intros. repeat break_match. simpl in *.
        repeat find_higher_order_rewrite.
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
        right.
        unfold add_ghost_msg in *.
        do_in_map. subst. simpl in *.
        apply in_map_iff. eauto.
    - unfold mgv_deghost in *. simpl in *.
      eapply RRIR_doLeader; eauto.
      + simpl in *. repeat break_match. simpl in *. eauto.
      + simpl in *.
        intros. repeat break_match; simpl in *;
        repeat find_higher_order_rewrite;
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
        right.
        unfold add_ghost_msg in *.
        do_in_map. subst. simpl in *.
        apply in_map_iff. eauto.
    - unfold mgv_deghost in *. simpl in *.
      eapply RRIR_doGenericServer; eauto.
      + simpl in *. repeat break_match. simpl in *. eauto.
      + simpl in *.
        intros. repeat break_match; simpl in *;
        repeat find_higher_order_rewrite;
        repeat break_match; congruence.
      + in_crush.
        find_apply_hyp_hyp. in_crush.
        right.
        unfold add_ghost_msg in *.
        do_in_map. subst. simpl in *.
        apply in_map_iff. eauto.
  Qed.

  Theorem msg_lift_prop :
    forall P,
      (forall net, refined_raft_intermediate_reachable net -> P net) ->
      (forall net, msg_refined_raft_intermediate_reachable net -> P (mgv_deghost net)).
  Proof.
    intros.
    eauto using simulation_1.
  Qed.

  Require Import DupDropReordering.

  Lemma step_f_star_raft_intermediate_reachable_extend :
    forall f net f' net' tr,
      @step_f_star _ _ raft_msg_refined_failure_params (f, net) (f', net') tr ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable net'.
  Proof.
    intros.
    prep_induction H.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - find_inversion. auto.
    - destruct x'. simpl in *.
      eapply MRRIR_step_f; [|eauto].
      eauto.
  Qed.

  Lemma map_subset :
    forall A B (f : A -> B) l l',
      (forall x, In x (map f l') -> In x (map f l)) ->
      exists l'',
        map f l' = map f l'' /\
        (forall x, In x l'' -> In x l).
  Proof.
    induction l'; simpl; intros.
    - exists nil. simpl in *. intuition.
    - assert (exists x, In x l /\ f x = f a).
      { specialize (H (f a)). concludes.
        find_apply_lem_hyp in_map_iff.
        firstorder.
      }
      specialize (IHl' ltac:(intuition)).
      repeat break_exists.
      break_and.
      exists (x :: x0).
      simpl. intuition; congruence.
  Qed.

  Lemma mgv_deghost_packet_mgv_ghost_packet_partial_inverses :
    forall p,
      (@mgv_deghost_packet _ _ _ ghost_log_params (mgv_ghost_packet p)) = p.
  Proof.
    intros.
    unfold mgv_deghost_packet, mgv_ghost_packet.
    simpl. destruct p; auto.
  Qed.
        
  Theorem simulation_2 :
    forall net,
      refined_raft_intermediate_reachable net ->
      exists rnet,
        net = mgv_deghost rnet /\
        msg_refined_raft_intermediate_reachable rnet.
  Proof.
    intros.
    induction H.
    - exists (mgv_reghost step_m_init). intuition.
        unfold mgv_reghost. constructor.
    - break_exists. break_and.
      apply mgv_ghost_simulation_2 with (gnet := x) in H0; auto.
      repeat (break_exists; intuition).
      subst.
      exists x0. intuition.
      eapply MRRIR_step_f; eauto.
    - break_exists. break_and.
      subst.
      assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (nwPackets x) ++ (@send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ _ ghost_log_params h (update_elections_data_input h inp (nwState (mgv_deghost x) h), d) l));
           nwState := st'
                                                       |})) by
          (unfold mgv_deghost in *; repeat break_match; simpl in *;
             eapply MRRIR_handleInput; repeat break_match; simpl in *; eauto;
           simpl in *; in_crush).
      pose proof map_subset _ _ mgv_deghost_packet
           (nwPackets x ++
                      @send_packets _ raft_msg_refined_multi_params h
                      (@add_ghost_msg _ _ _ ghost_log_params h
                                     (update_elections_data_input h inp
                                                                  (nwState (mgv_deghost x) h), d) l)) (map mgv_ghost_packet ps').
      forwards.
      {
        intros. rewrite map_map in *.
        do_in_map.
        subst.
        unfold mgv_deghost_packet.
        simpl in *.
        find_apply_hyp_hyp.
        rewrite map_app.
        in_crush.
        unfold add_ghost_msg.
        repeat rewrite map_map. simpl in *.
        right. in_crush.
      }
      concludes.
      break_exists_name dps'.
      intuition.
      exists {| nwPackets := dps'; nwState := st' |}.
      intuition.
      + rewrite map_map in H7.
        rewrite map_ext with (g := id) in H7; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
        rewrite map_id in *. subst.
        unfold mgv_deghost. simpl. auto.
      + eapply step_f_star_raft_intermediate_reachable_extend with (f := []); eauto using step_f_dup_drop_step.
        eapply step_f_dup_drop_step.
        apply dup_drop_reorder; auto.
        auto using packet_eq_dec.
    - break_exists. break_and.
      subst.
      unfold mgv_deghost in *. simpl in *.
      find_apply_lem_hyp map_partition.
      break_exists_name xs'. break_exists_name p'. break_exists_name ys'.
      intuition.
      subst. simpl in *.
      repeat break_match. simpl in *.
      subst. simpl in *.
      assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (xs' ++ ys') ++ (@send_packets _ raft_msg_refined_multi_params (pDst p') (@add_ghost_msg _ _ _ ghost_log_params (pDst p') (update_elections_data_net (pDst p') (pSrc p') (snd (pBody p')) (nwState  (pDst p')), d) l));
           nwState := st'
                                                       |})).
      { unfold mgv_deghost in *; repeat break_match; simpl in *.
        eapply MRRIR_handleMessage. eauto. simpl. eauto. simpl. eauto.
        simpl. eauto. simpl. auto.
        simpl in *; in_crush.
      }
      pose proof map_subset _ _ mgv_deghost_packet
           ((xs' ++ ys') ++
                      @send_packets _ raft_msg_refined_multi_params (pDst p')
                      (@add_ghost_msg _ _ _ ghost_log_params (pDst p')
                                      (update_elections_data_net (pDst p') (pSrc p')
                                                                 (snd (pBody p'))
                                                                 (nwState  (pDst p')), d) l)) (map mgv_ghost_packet ps').
      forwards.
      {
        intros. rewrite map_map in *.
        do_in_map.
        subst.
        unfold mgv_deghost_packet.
        simpl in *.
        find_apply_hyp_hyp.
        rewrite map_app.
        in_crush.
        - left. apply in_map_iff.
          eexists; intuition; eauto.
        - left. apply in_map_iff.
          eexists; intuition; eauto.
        - right.
          unfold add_ghost_msg.
          repeat rewrite map_map. simpl in *.
          in_crush.
      }
      concludes.
      break_exists_name dps'.
      intuition.
      exists {| nwPackets := dps'; nwState := st' |}.
      intuition.
      + rewrite map_map in H7.
        rewrite map_ext with (g := id) in H7; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
        rewrite map_id in *. subst.
        unfold mgv_deghost. simpl. auto.
      + eapply step_f_star_raft_intermediate_reachable_extend with (f := []); eauto using step_f_dup_drop_step.
        eapply step_f_dup_drop_step.
        apply dup_drop_reorder; auto.
        auto using packet_eq_dec.
    - break_exists. break_and.
      subst.
      assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (nwPackets x) ++ (@send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ _ ghost_log_params h (gd, d') ms));
           nwState := st'
                                                       |})).
      { unfold mgv_deghost in *; repeat break_match; simpl in *.
        eapply MRRIR_doLeader; repeat break_match; simpl in *; eauto;
        simpl in *; in_crush.
      }
      pose proof map_subset _ _ mgv_deghost_packet
           (nwPackets x ++
                      @send_packets _ raft_msg_refined_multi_params h
                      (@add_ghost_msg _ _ _ ghost_log_params h
                                     (gd, d') ms)) (map mgv_ghost_packet ps').
      forwards.
      {
        intros. rewrite map_map in *.
        do_in_map.
        subst.
        unfold mgv_deghost_packet.
        simpl in *.
        find_apply_hyp_hyp.
        rewrite map_app.
        in_crush.
        unfold add_ghost_msg.
        repeat rewrite map_map. simpl in *.
        right. in_crush.
      }
      concludes.
      break_exists_name dps'.
      intuition.
      exists {| nwPackets := dps'; nwState := st' |}.
      intuition.
      + rewrite map_map in H8.
        rewrite map_ext with (g := id) in H8; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
        rewrite map_id in *. subst.
        unfold mgv_deghost. simpl. auto.
      + eapply step_f_star_raft_intermediate_reachable_extend with (f := []); eauto using step_f_dup_drop_step.
        eapply step_f_dup_drop_step.
        apply dup_drop_reorder; auto.
        auto using packet_eq_dec.
    - break_exists. break_and.
      subst.
      assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (nwPackets x) ++ (@send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ _ ghost_log_params h (gd, d') ms));
           nwState := st'
                                                       |})).
      { unfold mgv_deghost in *; repeat break_match; simpl in *.
        eapply MRRIR_doGenericServer; repeat break_match; simpl in *; eauto;
        simpl in *; in_crush.
      }
      pose proof map_subset _ _ mgv_deghost_packet
           (nwPackets x ++
                      @send_packets _ raft_msg_refined_multi_params h
                      (@add_ghost_msg _ _ _ ghost_log_params h
                                     (gd, d') ms)) (map mgv_ghost_packet ps').
      forwards.
      {
        intros. rewrite map_map in *.
        do_in_map.
        subst.
        unfold mgv_deghost_packet.
        simpl in *.
        find_apply_hyp_hyp.
        rewrite map_app.
        in_crush.
        unfold add_ghost_msg.
        repeat rewrite map_map. simpl in *.
        right. in_crush.
      }
      concludes.
      break_exists_name dps'.
      intuition.
      exists {| nwPackets := dps'; nwState := st' |}.
      intuition.
      + rewrite map_map in H8.
        rewrite map_ext with (g := id) in H8; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
        rewrite map_id in *. subst.
        unfold mgv_deghost. simpl. auto.
      + eapply step_f_star_raft_intermediate_reachable_extend with (f := []); eauto using step_f_dup_drop_step.
        eapply step_f_dup_drop_step.
        apply dup_drop_reorder; auto.
        auto using packet_eq_dec.
  Qed.

  Theorem msg_lower_prop :
    forall P : _ -> Prop,
      (forall net, msg_refined_raft_intermediate_reachable net -> P (mgv_deghost net)) ->
      (forall net, refined_raft_intermediate_reachable net -> P net).
  Proof.
    intros.
    find_apply_lem_hyp simulation_2.
    break_exists. intuition. subst. eauto.
  Qed.

  Lemma deghost_spec :
    forall (net : @network _ raft_msg_refined_multi_params) h,
      nwState (mgv_deghost net) h = (nwState net h).
  Proof.
    intros.
    destruct net; auto.
  Qed.

  Context {rri : raft_refinement_interface}.
  
  Theorem lift_prop_all_the_way :
    forall (P : _ -> Prop),
      (forall net, raft_intermediate_reachable net -> P net) ->
      (forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> P (deghost (mgv_deghost net))).
  Proof.
    intros.
    find_eapply_lem_hyp msg_lift_prop; eauto.
    find_eapply_lem_hyp lift_prop; eauto.
  Qed.

  Theorem lower_prop_all_the_way :
    forall P : _ -> Prop,
      (forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> P (deghost (mgv_deghost net))) ->
      (forall net, raft_intermediate_reachable net -> P net).
  Proof.
    intros.
    eapply lower_prop; eauto.
    intros.
    pose proof msg_lower_prop (fun n => P (deghost n)).
    simpl in *. eauto.
  Qed.

    
  Instance rmri : raft_msg_refinement_interface.
  Proof.
    split.
    - exact msg_refined_raft_net_invariant.
    - exact msg_refined_raft_net_invariant'.
    - exact msg_lift_prop.
    - exact lift_prop_all_the_way.
    - exact msg_lower_prop.
    - exact lower_prop_all_the_way.
    - exact deghost_spec.
    - exact simulation_1.
  Qed.  
  
End RaftMsgRefinement.
