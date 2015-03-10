Require Import List.

Require Import VerdiTactics.
Require Import Net.
Require Import Raft.
Require Import RaftRefinementInterface.

Section LeaderCompleteness.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition directly_committed (net : network) (e : entry) :=
    exists quorum,
      NoDup quorum /\
      length quorum > div2 (length nodes) /\
      forall h,
        In h quorum ->
        In (eTerm e, e) (allEntries (fst (nwState net h))).

  Definition committed (net : network) (e : entry) (t : term) :=
    exists h e',
      eTerm e' <= t /\
      directly_committed net e' /\
      eIndex e <= eIndex e' /\
      In e (log (snd (nwState net h))) /\
      In e' (log (snd (nwState net h))).
      

  Definition leader_completeness_directly_committed net :=
    forall t e log h,
      directly_committed net e ->
      t > eTerm e ->
      In (t, log) (leaderLogs (fst (nwState net h))) ->
      In e log.

  Definition leader_completeness_committed net :=
    forall t t' e log h,
      committed net e t ->
      t' > t ->
      In (t', log) (leaderLogs (fst (nwState net h))) ->
      In e log.

  Definition leader_completeness net :=
    leader_completeness_directly_committed net /\ leader_completeness_committed net.

  Class leader_completeness_interface : Prop :=
    {
      leader_completeness_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leader_completeness net
    }.
  
End LeaderCompleteness.
