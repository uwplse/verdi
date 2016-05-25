Require Import Raft.
Require Import RaftRefinementInterface.
Require Import CommonDefinitions.
Require Import RefinementCommonDefinitions.

Section EveryEntryWasCreated.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition every_entry_was_created (net : network) : Prop :=
    forall e t h l,
      In (t, l) (leaderLogs (fst (nwState net h))) ->
      In e l ->
      term_was_created net (eTerm e).

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
  
  Class every_entry_was_created_interface : Prop :=
    {
      every_entry_was_created_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          every_entry_was_created net ;
      
      every_entry_was_created_in_any_log_invariant :
        forall net e,
          refined_raft_intermediate_reachable net ->
          in_any_log net e ->
          term_was_created net (eTerm e)
    }.
End EveryEntryWasCreated.
