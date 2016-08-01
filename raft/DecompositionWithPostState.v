Require Import FunctionalExtensionality.

Require Import Raft.

Section DecompositionWithPostState.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition raft_net_invariant_client_request' (P : network -> Prop) :=
    forall h net st' ps' out d l client id c,
      handleClientRequest h (nwState net h) client id c = (out, d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update name_eq_dec (nwState net) h d h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_timeout' (P : network -> Prop) :=
    forall net h st' ps' out d l,
      handleTimeout h (nwState net h) = (out, d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update name_eq_dec (nwState net) h d h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                               In p' (send_packets h l)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_append_entries' (P : network -> Prop) :=
    forall xs p ys net st' ps' d m t n pli plt es ci,
      handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (d, m) ->
      pBody p = AppendEntries t n pli plt es ci ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update name_eq_dec (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_append_entries_reply' (P : network -> Prop) :=
    forall xs p ys net st' ps' d m t es res,
      handleAppendEntriesReply (pDst p) (nwState net (pDst p)) (pSrc p) t es res = (d, m) ->
      pBody p = AppendEntriesReply t es res ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update name_eq_dec (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         In p' (send_packets (pDst p) m)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_request_vote' (P : network -> Prop) :=
    forall xs p ys net st' ps' d m t cid lli llt,
      handleRequestVote (pDst p) (nwState net (pDst p)) t (pSrc p) lli llt  = (d, m) ->
      pBody p = RequestVote t cid lli llt ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update name_eq_dec (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) m) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_request_vote_reply' (P : network -> Prop) :=
    forall xs p ys net st' ps' d t v,
      handleRequestVoteReply (pDst p) (nwState net (pDst p)) (pSrc p) t v = d ->
      pBody p = RequestVoteReply t v ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update name_eq_dec (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_do_leader' (P : network -> Prop) :=
    forall net st' ps' d h os d' ms,
      doLeader d h = (os, d', ms) ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwState net h = d ->
      (forall h', st' h' = update name_eq_dec (nwState net) h d' h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Definition raft_net_invariant_do_generic_server' (P : network -> Prop) :=
    forall net st' ps' d os d' ms h,
      doGenericServer h d = (os, d', ms) ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwState net h = d ->
      (forall h', st' h' = update name_eq_dec (nwState net) h d' h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h ms)) ->
      P (mkNetwork ps' st').

  Lemma raft_invariant_handle_message' P :
    forall xs p ys net st' ps' d l,
      raft_net_invariant_append_entries' P ->
      raft_net_invariant_append_entries_reply' P ->
      raft_net_invariant_request_vote' P ->
      raft_net_invariant_request_vote_reply' P ->
      handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update name_eq_dec (nwState net) (pDst p) d h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                             In p' (send_packets (pDst p) l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleMessage in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop raft_net_invariant_request_vote'|
     eapply_prop raft_net_invariant_request_vote_reply'|
     eapply_prop raft_net_invariant_append_entries'|
     eapply_prop raft_net_invariant_append_entries_reply']; eauto;
    unfold send_packets in *; simpl in *; intros; find_apply_hyp_hyp; intuition.
  Qed.

  Lemma raft_invariant_handle_input' P :
    forall h inp net st' ps' out d l,
      raft_net_invariant_timeout' P ->
      raft_net_invariant_client_request' P ->
      handleInput h inp (nwState net h) = (out, d, l) ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update name_eq_dec (nwState net) h d h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h l)) ->
      P (mkNetwork ps' st').
  Proof.
    intros.
    unfold handleInput in *.
    break_match; repeat break_let; repeat find_inversion;
    [eapply_prop raft_net_invariant_timeout'|
     eapply_prop raft_net_invariant_client_request']; eauto;
    unfold send_packets in *; simpl in *; intros; find_apply_hyp_hyp; intuition.
  Qed.

  Definition raft_net_invariant_reboot' (P : network -> Prop) :=
    forall net net' d h d',
      reboot d = d' ->
      P net ->
      raft_intermediate_reachable net ->
      raft_intermediate_reachable net' ->
      nwState net h = d ->
      (forall h', nwState net' h' = update name_eq_dec (nwState net) h d' h') ->
      nwPackets net = nwPackets net' ->
      P net'.

  Theorem raft_net_invariant' :
    forall P net,
      raft_net_invariant_init P ->
      raft_net_invariant_client_request' P ->
      raft_net_invariant_timeout' P ->
      raft_net_invariant_append_entries' P ->
      raft_net_invariant_append_entries_reply' P ->
      raft_net_invariant_request_vote' P ->
      raft_net_invariant_request_vote_reply' P ->
      raft_net_invariant_do_leader' P ->
      raft_net_invariant_do_generic_server' P ->
      raft_net_invariant_state_same_packet_subset P ->
      raft_net_invariant_reboot' P ->
      raft_intermediate_reachable net ->
      P net.
  Proof.
    intros.
    induction H10.
    - intuition.
    -  match goal with [H : step_f _ _ _ |- _ ] => invcs H end.
       + unfold RaftNetHandler in *. repeat break_let.
         repeat find_inversion.
         assert
           (HREACH1 : raft_intermediate_reachable
              {|
                nwPackets := (send_packets (pDst p) l0) ++ xs ++ ys;
                nwState := update name_eq_dec (nwState net) (pDst p) r
              |}) by (eapply RIR_handleMessage; eauto; in_crush).
         assert
           (HREACH2 : raft_intermediate_reachable
              {|
                nwPackets := (send_packets (pDst p) (l0 ++ l1)) ++ xs ++ ys;
                nwState := (update name_eq_dec (update name_eq_dec (nwState net) (pDst p) r) (pDst p) r0)
              |}) by (eapply RIR_doLeader; eauto;
                      [simpl in *; break_if; try congruence; eauto| in_crush]).
         assert
           (HREACH3 : raft_intermediate_reachable
              {|
                nwPackets := (send_packets (pDst p) (l0 ++ l1 ++ l3)) ++ xs ++ ys;
                nwState := (update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) (pDst p) r) (pDst p) r0) (pDst p) d)
              |}).
         { eapply RIR_doGenericServer; eauto.
           - simpl in *. break_if; try congruence; eauto.
           - intros. simpl.
             repeat do_in_app. intuition; try solve [in_crush].
             simpl in *. do_in_map. subst.
             do_in_app. intuition; try do_in_app; intuition.
             + left. in_crush. left. in_crush.
             + left. in_crush. left. in_crush.
             + in_crush. }
         eapply_prop raft_net_invariant_do_generic_server'. eauto.
         eapply_prop raft_net_invariant_do_leader'. eauto. 
         eapply raft_invariant_handle_message' with (P := P);
           try match goal with
                 | |- context [ update ] =>
                   eauto
               end;
           eauto; try solve [in_crush].
         auto.
         apply HREACH2.
         simpl. break_if; intuition eauto.
         intros. simpl. repeat break_if; subst; eauto.
         simpl. in_crush. auto.
         {
           simpl in HREACH3.
           match goal with
             | _ : raft_intermediate_reachable (mkNetwork ?p ?s) |-
                   raft_intermediate_reachable (mkNetwork ?p' ?s') =>
               enough (s' = s) by (repeat find_rewrite; auto)
           end.
           apply functional_extensionality.
           intros. repeat break_if; subst; eauto.
         }
         simpl. break_if; congruence.
         simpl. intros.
         break_if; subst;
         repeat rewrite update_same by auto;
         repeat rewrite update_neq by auto; auto.
         simpl.
         intros. simpl.
         repeat do_in_app. intuition; try solve [in_crush].
         simpl in *. do_in_map. subst.
         do_in_app. intuition; try do_in_app; intuition.
         * left. in_crush. left. in_crush.
         * left. in_crush. left. in_crush.
         * in_crush.
       + unfold RaftInputHandler in *. repeat break_let.
         repeat find_inversion.
         assert
           (HREACH1 : raft_intermediate_reachable
              {|
                nwPackets := (send_packets h l0) ++ (nwPackets net);
                nwState := update name_eq_dec (nwState net) h r
              |}) by (eapply RIR_handleInput; eauto; in_crush).
         assert
           (HREACH2 : raft_intermediate_reachable
              {|
                nwPackets := (send_packets h (l0 ++ l2)) ++ (nwPackets net);
                nwState := (update name_eq_dec (update name_eq_dec (nwState net) h r) h r0)
              |}) by (eapply RIR_doLeader; eauto;
                      [simpl in *; break_if; try congruence; eauto| in_crush]).
         assert
           (HREACH3 : raft_intermediate_reachable
              {|
                nwPackets := (send_packets h (l0 ++ l2 ++ l4)) ++ (nwPackets net);
                nwState := (update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h r) h r0) h d)
              |}).
          { eapply RIR_doGenericServer; eauto.
           - simpl in *. break_if; try congruence; eauto.
           - intros. simpl. 
             repeat do_in_app. intuition; try solve [in_crush].
             simpl in *. do_in_map. subst.
             do_in_app. intuition; try do_in_app; intuition.
             + left. in_crush. left. in_crush.
             + left. in_crush. left. in_crush.
             + in_crush. }
         eapply_prop raft_net_invariant_do_generic_server'. eauto.
         eapply_prop raft_net_invariant_do_leader'. eauto.
         eapply raft_invariant_handle_input' with (P := P);
           try match goal with
                 | |- context [ update ] =>
                   eauto
               end;
           eauto; try solve [in_crush].
         auto.
         apply HREACH2.
         simpl. break_if; intuition eauto.
         eauto. simpl. in_crush.
         auto.
         {
           simpl in HREACH3.
           match goal with
             | _ : raft_intermediate_reachable (mkNetwork ?p ?s) |-
                   raft_intermediate_reachable (mkNetwork ?p ?s') =>
               enough (s' = s) by (repeat find_rewrite; auto)
           end.
           apply functional_extensionality.
           intros. repeat break_if; subst; eauto.
         } 
         simpl. break_if; congruence.
         simpl. intros. repeat break_if; subst; eauto.
         intros. simpl.
         repeat do_in_app. intuition; try solve [in_crush].
         simpl in *. do_in_map. subst.
         do_in_app. intuition; try do_in_app; intuition.
         * left. in_crush. left. in_crush.
         * left. in_crush. left. in_crush.
         * in_crush.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end. 
         eapply_prop raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + match goal with
           | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] =>
             assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) ->
                          In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush)
         end. 
         eapply_prop raft_net_invariant_state_same_packet_subset; [|eauto|idtac|];
         eauto.
       + auto.
       + eapply_prop raft_net_invariant_reboot'; eauto;
         intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
         eapply RIR_step_f; eauto.
         now econstructor; eauto.
    - eapply raft_invariant_handle_input'; eauto using RIR_handleInput.
    - eapply raft_invariant_handle_message'; eauto using RIR_handleMessage.
    - eapply_prop raft_net_invariant_do_leader'; eauto using RIR_doLeader.
    - eapply_prop raft_net_invariant_do_generic_server'; eauto using RIR_doGenericServer.
  Qed.

End DecompositionWithPostState.
