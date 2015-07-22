Require Import List.
Import ListNotations.
Require Import Omega.
Require Import FunctionalExtensionality.


Require Import VerdiTactics.
Require Import Net.
Require Import Util.
Require Import Raft.
Require Import RaftRefinementInterface.

Require Import CommonTheorems.
Require Import SpecLemmas.

Require Import UpdateLemmas.
Require Import DecompositionWithPostState.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import AppendEntriesRequestReplyRefinedCorrespondenceInterface.

Require Import DupDropReordering.

Section AppendEntriesRequestReplyRefinedCorrespondence.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Instance aerrrci : append_entries_request_reply_refined_correspondence_interface.
  Admitted.
End AppendEntriesRequestReplyRefinedCorrespondence.
