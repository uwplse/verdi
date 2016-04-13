Require Import Chord.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Extraction "ExtractedChord.ml" addr addr_eq_dec payload data start_handler recv_handler tick_handler timeout_handler client_payload request_payload can_be_client can_be_node closes_request.
