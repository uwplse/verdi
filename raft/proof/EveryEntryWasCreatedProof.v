Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.

Require Import LeadersHaveLeaderLogsInterface.
Require Import EveryEntryWasCreatedInterface.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lhlli : leaders_have_leaderLogs_interface}.

  Inductive in_any_log (net : network) (e : entry) : Prop :=
  | in_log : forall h, In e (log (snd (nwState net h))) ->
                  in_any_log net e
  | in_aer : forall p es, In p (nwPackets net) ->
                     mEntries (pBody p) = Some es ->
                     In e es ->
                     in_any_log net e
  | in_ll : forall h t ll, In (t, ll) (leaderLogs (fst (nwState net h))) ->
                      In e ll ->
                      in_any_log net e.

  (* proof sketch: prove for in_any_log. the only time new entries
  come into the system is on a leader, and leaders have leaderLogs in
  their term.  *)

  Instance eewci : every_entry_was_created_interface.
  Admitted.

End EveryEntryWasCreated.
