Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import Sumbool.

Require Import Util.
Require Import Net.
Require Import RaftState.
Require Import Raft.
Require Import VerdiTactics.

Require Import RaftRefinementInterface.

Section RaftMsgRefinementInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition ghost_log : Type := list entry.

  Lemma ghost_log_eq_dec : forall x y : ghost_log, {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply entry_eq_dec.
  Qed.

  Definition write_ghost_log (h : name) (st : @data raft_refined_base_params) : ghost_log := log (snd st).

  Instance ghost_log_params : MsgGhostFailureParams raft_refined_failure_params :=
    {| ghost_msg := ghost_log ;
       ghost_msg_eq_dec := ghost_log_eq_dec ;
       ghost_msg_default := [] ;
       write_ghost_msg := write_ghost_log
    |}.

  Definition raft_msg_refined_base_params := mgv_refined_base_params.
  Definition raft_msg_refined_multi_params := mgv_refined_multi_params.
  Definition raft_msg_refined_failure_params := mgv_refined_failure_params.

  Hint Extern 3 (@BaseParams) => apply raft_msg_refined_base_params : typeclass_instances.
  Hint Extern 3 (@MultiParams _) => apply raft_msg_refined_multi_params : typeclass_instances.
  Hint Extern 3 (@FailureParams _ _) => apply raft_msg_refined_failure_params : typeclass_instances.

  Inductive msg_refined_raft_intermediate_reachable : network -> Prop :=
  | MRRIR_init : msg_refined_raft_intermediate_reachable step_m_init
  | MRRIR_step_f :
      forall failed net failed' net' out,
        msg_refined_raft_intermediate_reachable net ->
        step_f (failed, net) (failed', net') out ->
        msg_refined_raft_intermediate_reachable net'
  | MRRIR_handleInput :
      forall net h inp gd out d l ps' st',
        msg_refined_raft_intermediate_reachable net ->
        handleInput h inp (snd (nwState net h)) = (out, d, l) ->
        update_elections_data_input h inp (nwState net h) = gd ->
        (forall h', st' h' = update (nwState net) h (gd, d) h') ->
        (forall p', In p' ps' -> In p' (nwPackets net) \/
                           In p' (send_packets h (add_ghost_msg h (gd, d) l))) ->
        msg_refined_raft_intermediate_reachable (mkNetwork ps' st')
  | MRRIR_handleMessage :
      forall p net xs ys st' ps' gd d l,
        msg_refined_raft_intermediate_reachable net ->
        handleMessage (pSrc p) (pDst p) (snd (pBody p)) (snd (nwState net (pDst p))) = (d, l) ->
        update_elections_data_net (pDst p) (pSrc p) (snd (pBody p)) (nwState net (pDst p)) = gd ->
        nwPackets net = xs ++ p :: ys ->
        (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
        (forall p', In p' ps' -> In p' (xs ++ ys) \/
                           In p' (send_packets (pDst p) (@add_ghost_msg _ _ _ ghost_log_params (pDst p) (gd, d) l))) ->
        msg_refined_raft_intermediate_reachable (mkNetwork ps' st')
  | MRRIR_doLeader :
      forall net st' ps' h os gd d d' ms,
        msg_refined_raft_intermediate_reachable net ->
        doLeader d h = (os, d', ms) ->
        nwState net h = (gd, d) ->
        (forall h', st' h' = update (nwState net) h (gd, d') h') ->
        (forall p, In p ps' -> In p (nwPackets net) \/
                         In p (send_packets h (add_ghost_msg h (gd, d') ms))) ->
        msg_refined_raft_intermediate_reachable (mkNetwork ps' st')
  | MRRIR_doGenericServer :
      forall net st' ps' os gd d d' ms h,
        msg_refined_raft_intermediate_reachable net ->
        doGenericServer h d = (os, d', ms) ->
        nwState net h = (gd, d) ->
        (forall h', st' h' = update (nwState net) h (gd, d') h') ->
        (forall p, In p ps' -> In p (nwPackets net) \/
                         In p (send_packets h (add_ghost_msg h (gd, d') ms))) ->
        msg_refined_raft_intermediate_reachable (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_client_request (P : network -> Prop) :=
    forall h net st' ps' gd out d l client id c,
      handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) ->
      gd = update_elections_data_client_request h (nwState net h) client id c ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h (add_ghost_msg h (gd, d) l))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_timeout (P : network -> Prop) :=
    forall net h st' ps' gd out d l,
      handleTimeout h (snd (nwState net h)) = (out, d, l) ->
      gd = update_elections_data_timeout h (nwState net h) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                               In p' (send_packets h (add_ghost_msg h (gd, d) l))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_append_entries (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t n pli plt es ci,
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) ->
      gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) (write_ghost_log (pDst p) (gd, d), m)) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_append_entries_reply (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t es res,
      handleAppendEntriesReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t es res = (d, m) ->
      gd = (fst (nwState net (pDst p))) ->
      snd (pBody p) = AppendEntriesReply t es res ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         In p' (send_packets (pDst p) (@add_ghost_msg _ _ _ ghost_log_params (pDst p) (gd, d) m))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_request_vote (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t cid lli llt,
      handleRequestVote (pDst p) (snd (nwState net (pDst p))) t (pSrc p) lli llt  = (d, m) ->
      gd = update_elections_data_requestVote (pDst p) (pSrc p) t (pSrc p) lli llt (nwState net (pDst p)) ->
      snd (pBody p) = RequestVote t cid lli llt ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) (write_ghost_log (pDst p) (gd, d), m)) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_request_vote_reply (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d t v,
      handleRequestVoteReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t v = d ->
      gd = update_elections_data_requestVoteReply (pDst p) (pSrc p) t v (nwState net (pDst p)) ->
      snd (pBody p) = RequestVoteReply t v ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_do_leader (P : network -> Prop) :=
    forall net st' ps' gd d h os d' ms,
      doLeader d h = (os, d', ms) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h (add_ghost_msg h (gd, d') ms))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_do_generic_server (P : network -> Prop) :=
    forall net st' ps' gd d os d' ms h,
      doGenericServer h d = (os, d', ms) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h (add_ghost_msg h (gd, d') ms))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_state_same_packet_subset (P : network -> Prop) :=
    forall net net',
      (forall h, nwState net h = nwState net' h) ->
      (forall p, In p (nwPackets net') -> In p (nwPackets net)) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      P net'.

  Definition msg_refined_raft_net_invariant_reboot (P : network -> Prop) :=
    forall net net' gd d h d',
      reboot d = d' ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      nwState net h = (gd, d) ->
      (forall h', nwState net' h' = update (nwState net) h (gd, d') h') ->
      nwPackets net = nwPackets net' ->
      P net'.

  Definition msg_refined_raft_net_invariant_init (P : network -> Prop) :=
    P step_m_init.
  
  Definition msg_refined_raft_net_invariant_client_request' (P : network -> Prop) :=
    forall h net st' ps' gd out d l client id c,
      handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) ->
      gd = update_elections_data_client_request h (nwState net h) client id c ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                         In p' (send_packets h (add_ghost_msg h (gd, d) l))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_timeout' (P : network -> Prop) :=
    forall net h st' ps' gd out d l,
      handleTimeout h (snd (nwState net h)) = (out, d, l) ->
      gd = update_elections_data_timeout h (nwState net h) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      (forall h', st' h' = update (nwState net) h (gd, d) h') ->
      (forall p', In p' ps' -> In p' (nwPackets net) \/
                               In p' (send_packets h (add_ghost_msg h (gd, d) l))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_append_entries' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t n pli plt es ci,
      handleAppendEntries (pDst p) (snd (nwState net (pDst p))) t n pli plt es ci = (d, m) ->
      gd = update_elections_data_appendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) (write_ghost_log (pDst p) (gd, d), m)) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_append_entries_reply' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t es res,
      handleAppendEntriesReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t es res = (d, m) ->
      gd = (fst (nwState net (pDst p))) ->
      snd (pBody p) = AppendEntriesReply t es res ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         In p' (send_packets (pDst p) (@add_ghost_msg _ _ _ ghost_log_params (pDst p) (gd, d) m))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_request_vote' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d m t cid lli llt,
      handleRequestVote (pDst p) (snd (nwState net (pDst p))) t (pSrc p) lli llt  = (d, m) ->
      gd = update_elections_data_requestVote (pDst p) (pSrc p) t (pSrc p) lli llt (nwState net (pDst p)) ->
      snd (pBody p) = RequestVote t cid lli llt ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys) \/
                         p' = mkPacket (pDst p) (pSrc p) (write_ghost_log (pDst p) (gd, d), m)) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_request_vote_reply' (P : network -> Prop) :=
    forall xs p ys net st' ps' gd d t v,
      handleRequestVoteReply (pDst p) (snd (nwState net (pDst p))) (pSrc p) t v = d ->
      gd = update_elections_data_requestVoteReply (pDst p) (pSrc p) t v (nwState net (pDst p)) ->
      snd (pBody p) = RequestVoteReply t v ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwPackets net = xs ++ p :: ys ->
      (forall h, st' h = update (nwState net) (pDst p) (gd, d) h) ->
      (forall p', In p' ps' -> In p' (xs ++ ys)) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_do_leader' (P : network -> Prop) :=
    forall net st' ps' gd d h os d' ms,
      doLeader d h = (os, d', ms) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h (add_ghost_msg h (gd, d') ms))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_do_generic_server' (P : network -> Prop) :=
    forall net st' ps' gd d os d' ms h,
      doGenericServer h d = (os, d', ms) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable (mkNetwork ps' st') ->
      nwState net h = (gd, d) ->
      (forall h', st' h' = update (nwState net) h (gd, d') h') ->
      (forall p, In p ps' -> In p (nwPackets net) \/
                             In p (send_packets h (add_ghost_msg h (gd, d') ms))) ->
      P (mkNetwork ps' st').

  Definition msg_refined_raft_net_invariant_state_same_packet_subset' (P : network -> Prop) :=
    forall net net',
      (forall h, nwState net h = nwState net' h) ->
      (forall p, In p (nwPackets net') -> In p (nwPackets net)) ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable net' ->
      P net'.

  Definition msg_refined_raft_net_invariant_reboot' (P : network -> Prop) :=
    forall net net' gd d h d',
      reboot d = d' ->
      P net ->
      msg_refined_raft_intermediate_reachable net ->
      msg_refined_raft_intermediate_reachable net' ->
      nwState net h = (gd, d) ->
      (forall h', nwState net' h' = update (nwState net) h (gd, d') h') ->
      nwPackets net = nwPackets net' ->
      P net'.

  Lemma msg_refined_raft_net_invariant_client_request'_weak :
    forall net,
      msg_refined_raft_net_invariant_client_request net ->
      msg_refined_raft_net_invariant_client_request' net.
  Proof.
    unfold msg_refined_raft_net_invariant_client_request, msg_refined_raft_net_invariant_client_request'.
    intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_timeout'_weak :
    forall net,
      msg_refined_raft_net_invariant_timeout net ->
      msg_refined_raft_net_invariant_timeout' net.
    Proof.
      unfold msg_refined_raft_net_invariant_timeout, msg_refined_raft_net_invariant_timeout'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_append_entries'_weak :
    forall net,
      msg_refined_raft_net_invariant_append_entries net ->
      msg_refined_raft_net_invariant_append_entries' net.
    Proof.
      unfold msg_refined_raft_net_invariant_append_entries, msg_refined_raft_net_invariant_append_entries'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_append_entries_reply'_weak :
    forall net,
      msg_refined_raft_net_invariant_append_entries_reply net ->
      msg_refined_raft_net_invariant_append_entries_reply' net.
    Proof.
      unfold msg_refined_raft_net_invariant_append_entries_reply, msg_refined_raft_net_invariant_append_entries_reply'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_request_vote'_weak :
    forall net,
      msg_refined_raft_net_invariant_request_vote net ->
      msg_refined_raft_net_invariant_request_vote' net.
    Proof.
      unfold msg_refined_raft_net_invariant_request_vote, msg_refined_raft_net_invariant_request_vote'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_request_vote_reply'_weak :
    forall net,
      msg_refined_raft_net_invariant_request_vote_reply net ->
      msg_refined_raft_net_invariant_request_vote_reply' net.
    Proof.
      unfold msg_refined_raft_net_invariant_request_vote_reply, msg_refined_raft_net_invariant_request_vote_reply'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_do_leader'_weak :
    forall net,
      msg_refined_raft_net_invariant_do_leader net ->
      msg_refined_raft_net_invariant_do_leader' net.
    Proof.
      unfold msg_refined_raft_net_invariant_do_leader, msg_refined_raft_net_invariant_do_leader'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_do_generic_server'_weak :
    forall net,
      msg_refined_raft_net_invariant_do_generic_server net ->
      msg_refined_raft_net_invariant_do_generic_server' net.
    Proof.
      unfold msg_refined_raft_net_invariant_do_generic_server, msg_refined_raft_net_invariant_do_generic_server'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_reboot'_weak :
    forall net,
      msg_refined_raft_net_invariant_reboot net ->
      msg_refined_raft_net_invariant_reboot' net.
    Proof.
      unfold msg_refined_raft_net_invariant_reboot, msg_refined_raft_net_invariant_reboot'.
      intuition eauto.
  Qed.

  Lemma msg_refined_raft_net_invariant_subset'_weak :
    forall net,
      msg_refined_raft_net_invariant_state_same_packet_subset net ->
      msg_refined_raft_net_invariant_state_same_packet_subset' net.
  Proof.
    unfold msg_refined_raft_net_invariant_state_same_packet_subset, msg_refined_raft_net_invariant_state_same_packet_subset'.
    intuition eauto.
  Qed.


  Class raft_msg_refinement_interface : Prop :=
    {
      msg_refined_raft_net_invariant :
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
          P net;
      msg_refined_raft_net_invariant' :
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
          P net;
      msg_lift_prop :
        forall (P : _ -> Prop),
          (forall net, refined_raft_intermediate_reachable net -> P net) ->
          (forall net, msg_refined_raft_intermediate_reachable net -> P (mgv_deghost net));
      msg_lift_prop_all_the_way :
        forall (P : _ -> Prop),
          (forall net, raft_intermediate_reachable net -> P net) ->
          (forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> P (deghost (mgv_deghost net)));
      msg_lower_prop :
        forall P : _ -> Prop,
          (forall net, msg_refined_raft_intermediate_reachable net -> P (mgv_deghost net)) ->
          (forall net, refined_raft_intermediate_reachable net -> P net);
      msg_lower_prop_all_the_way :
        forall P : _ -> Prop,
          (forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> P (deghost (mgv_deghost net))) ->
          (forall net, raft_intermediate_reachable net -> P net);
      msg_deghost_spec :
        forall (net : @network _ raft_msg_refined_multi_params) h,
          nwState (mgv_deghost net) h = nwState net h;
      msg_simulation_1 :
        forall net,
          msg_refined_raft_intermediate_reachable net ->
          refined_raft_intermediate_reachable (mgv_deghost net)
    }.


End RaftMsgRefinementInterface.

Hint Extern 3 (@BaseParams) => apply raft_msg_refined_base_params : typeclass_instances.
Hint Extern 3 (@MultiParams _) => apply raft_msg_refined_multi_params : typeclass_instances.
Hint Extern 3 (@FailureParams _ _) => apply raft_msg_refined_failure_params : typeclass_instances.
