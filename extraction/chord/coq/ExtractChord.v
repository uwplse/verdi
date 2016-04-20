Require Import Arith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Chord.

Definition SUCC_LIST_LEN := 5.

Definition hash (a : addr) : id :=
  a mod 256.

Definition handleNet : addr -> addr -> payload -> data -> data * list (addr * payload) :=
  recv_handler SUCC_LIST_LEN hash.

Definition init : addr -> list addr -> data * list (addr * payload) :=
  start_handler SUCC_LIST_LEN hash.

Definition handleTick : addr -> data -> data * list (addr * payload) :=
  tick_handler hash.

Definition handleTimeout : addr -> addr -> data -> data * list (addr * payload) :=
  timeout_handler hash.

Extraction "ExtractedChord.ml" init handleNet handleTick handleTimeout is_request closes_request.