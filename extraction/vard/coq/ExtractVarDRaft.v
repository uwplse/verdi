Require Import Verdi.
Require Import VarD.
Require Import VarDRaft.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import ExtrOcamlBasicExt.
Require Import ExtrOcamlNatIntExt.

Require Import ExtrOcamlBool.
Require Import ExtrOcamlList.
Require Import ExtrOcamlFin.

Extraction "extraction/vard/coq/VarDRaft.ml" seq vard_raft_base_params vard_raft_multi_params vard_raft_failure_params.
