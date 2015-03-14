Require Import List.

Require Import Net.
Require Import Raft.

Require Import CommonDefinitions.

Section SortedInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition logs_sorted_host net :=
    forall h,
      sorted (log (nwState net h)).

  Definition logs_sorted_nw net :=
    forall p t n prevT prevI entries c,
      In p (nwPackets net) ->
      (pBody p) = AppendEntries t n prevT prevI entries c ->
      sorted entries.

  Definition packets_gt_prevIndex net :=
    forall p t n pli plt entries c e,
      In p (nwPackets net) ->
      (pBody p) = AppendEntries t n pli plt entries c ->
      In e entries ->
      eIndex e > pli.

  Definition packets_ge_prevTerm net :=
    forall p t n pli plt entries c e,
      In p (nwPackets net) ->
      (pBody p) = AppendEntries t n pli plt entries c ->
      In e entries ->
      eTerm e >= plt.

  Definition logs_sorted net :=
    logs_sorted_host net /\ logs_sorted_nw net /\
    packets_gt_prevIndex net /\ packets_ge_prevTerm net.

  Class sorted_interface : Prop :=
    {
      handleAppendEntries_logs_sorted :
        forall net p t n pli plt es ci st' m,
          raft_intermediate_reachable net ->
          logs_sorted net ->
          handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci =
          (st', m) ->
          pBody p = AppendEntries t n pli plt es ci ->
          In p (nwPackets net) ->
          sorted (log st');
      handleClientRequest_logs_sorted :
        forall h client id c out st l net,
          handleClientRequest h (nwState net h) client id c = (out, st, l) ->
          raft_intermediate_reachable net ->
          logs_sorted_host net ->
          sorted (log st);
      logs_sorted_invariant :
        forall net,
          raft_intermediate_reachable net ->
          logs_sorted net
    }.
End SortedInterface.