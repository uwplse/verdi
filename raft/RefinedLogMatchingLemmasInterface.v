Require Import List.
Import ListNotations.

Require Import Util.
Require Import Net.

Require Import CommonTheorems.

Require Import Raft.
Require Import RaftRefinementInterface.

Section RefinedLogMatchingLemmas.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition entries_contiguous_nw net :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      contiguous_range_exact_lo es pli.

  Definition entries_gt_0_nw net :=
    forall p t n pli plt es ci e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e es ->
      eIndex e > 0.

  Definition entries_sorted_nw net :=
    forall p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      sorted es.

  Definition entries_gt_0 net :=
    forall h e,
      In e (log (snd (nwState net h))) ->
      eIndex e > 0.  

  Definition entries_contiguous net :=
    forall h,
      contiguous_range_exact_lo (log (snd (nwState net h))) 0.
  
  Class refined_log_matching_lemmas_interface : Prop :=
    {
      entries_contiguous_nw_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          entries_contiguous_nw net;
      entries_gt_0_nw_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          entries_gt_0_nw net;
      entries_sorted_nw_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          entries_sorted_nw net;
      entries_gt_0_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          entries_gt_0 net;
      entries_contiguous_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          entries_contiguous net
    }.
End RefinedLogMatchingLemmas.
