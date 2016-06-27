Require Import Chord.
Require Import LabeledDynamicNet.
Import List.
Require Import infseq.

Section LabeledChord.
  Variable SUCC_LIST_LEN : nat.
  Variable hash : addr -> id.

  Notation msg := (msg addr payload).
  Notation global_state := (global_state addr payload data timeout).
  Notation msgs := (msgs addr payload data timeout).
  Notation e_recv := (e_recv addr payload timeout).
  Notation trace := (trace addr payload data timeout).

  Inductive label :=
  | RecvMsg : addr -> addr -> payload -> label
  | Timeout : addr -> timeout -> label
  | Tau : label.

  Definition label_eq_dec : forall x y : label, {x = y} + {x <> y}.  
  Proof.
    decide equality; eauto using addr_eq_dec, payload_eq_dec, timeout_eq_dec.
  Defined.

  Definition label_silent := Tau.

  Notation occ_gst := (occ_gst addr payload data timeout label).
  Notation occurrence := (occurrence addr payload data timeout label).

  Definition timeout_handler (h : addr) (st : data) (t : timeout) :=
    (timeout_handler hash h st t, Timeout h t).

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) :=
    (recv_handler SUCC_LIST_LEN hash src dst st msg, RecvMsg src dst msg).

  (* todo *)
  Variable extra_constraints : gpred addr payload data timeout.
  Print labeled_step_dynamic.
  Notation labeled_step_dynamic := (labeled_step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation lb_execution := (lb_execution addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation l_enabled := (l_enabled addr addr_eq_dec payload data timeout timeout_eq_dec label label_silent recv_handler timeout_handler extra_constraints).
  Notation occurred := (occurred addr payload data timeout label).

  Lemma RecvMsg_enabled_until_occurred :
    forall s,
      lb_execution s ->
      forall src dst m,
        In (dst, (src, m)) (msgs (occ_gst (hd s))) ->
        until (now (l_enabled (RecvMsg src dst m)))
              (now (occurred (RecvMsg src dst m)))
              s.
  Proof.
    cofix.
    intros.
  Abort.
End LabeledChord.