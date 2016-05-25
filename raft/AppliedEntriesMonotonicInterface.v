Require Import Raft.

Require Import CommonDefinitions.

Section AppliedEntriesMonotonicInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Class applied_entries_monotonic_interface :=
    {
      applied_entries_monotonic' :
        forall failed net failed' net' os,
          raft_intermediate_reachable net ->
          (@step_f _ _ failure_params (failed, net) (failed', net') os) ->
          exists es,
            applied_entries (nwState net') = applied_entries (nwState net) ++ es ;
      applied_entries_monotonic :
        forall e failed net failed' net' os,
          raft_intermediate_reachable net ->
          (@step_f _ _ failure_params (failed, net) (failed', net') os) ->
          In e (applied_entries (nwState net)) ->
          In e (applied_entries (nwState net'))
    }.
End AppliedEntriesMonotonicInterface.
