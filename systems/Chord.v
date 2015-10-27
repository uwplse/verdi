Require Import Arith.
Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.

Require Import DynamicNet.

Require Import String.

Definition addr := nat.

(* data for a given node *)
Record data :=
       { succ : addr;
         succ2 : addr;
         pred : addr;
         bestsucc : addr }.

Inductive payload :=
(* join event *)
| Join : payload
| LookupMySucc : addr -> payload
| FoundYourSucc : addr -> payload
(* stabilize event *)
| LookupYourPred : payload
| FoundMyPred : addr -> payload
(* notify event *)
| NotifySucc : payload.