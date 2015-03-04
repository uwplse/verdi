Require Import List.
Import ListNotations.
Require Import Arith.

Require Import Net.
Require Import Util.
Require Import VerdiTactics.

Require Import Raft.
Require Import CommonDefinitions.
Require Import TraceUtil.

Section OutputCorrect.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Class output_correct_interface : Prop :=
    {
      output_correct :
        forall client id out failed net tr,
          step_f_star step_f_init (failed, net) tr ->
          in_output_trace client id out tr ->
          exists xs e ys tr' st' i,
            deduplicate_log (applied_entries (nwState net)) = xs ++ e :: ys /\
            eClient e = client /\
            eId e = id /\
            eInput e = i /\
            execute_log (xs ++ [e]) = (tr', st') /\
            hd_error (rev tr') = Some (i, out)
    }.
End OutputCorrect.
