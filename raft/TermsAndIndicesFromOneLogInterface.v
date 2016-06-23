Require Import Raft.

Require Import CommonDefinitions.

Section TermsAndIndicesFromOneLogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition terms_and_indices_from_one_log (net : network) : Prop :=
    forall h,
      terms_and_indices_from_one (log (nwState net h)).

  Definition terms_and_indices_from_one_log_nw (net : network) : Prop :=
    forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
      In p (nwPackets net) ->
      pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit ->
      terms_and_indices_from_one entries.

  Class terms_and_indices_from_one_log_interface : Prop := {
    terms_and_indices_from_one_log_invariant : forall net,
      raft_intermediate_reachable net ->
      terms_and_indices_from_one_log net;
    terms_and_indices_from_one_log_nw_invariant : forall net,
      raft_intermediate_reachable net ->
      terms_and_indices_from_one_log_nw net
  }.
End TermsAndIndicesFromOneLogInterface.
