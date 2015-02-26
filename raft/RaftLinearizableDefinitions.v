Require Import List.
Import ListNotations.

Require Import VerdiTactics.
Require Import Util.
Require Import Net.

Require Import Raft.

Section RaftLinearizableDefinitions.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition project_input_keys (tr : list (name * (raft_input + list raft_output))) : list (nat * nat) :=
    filterMap (fun x => match x with
                          | (_, inl (ClientRequest client id _)) => Some (client, id)
                          | _ => None
                        end) tr.

  Definition input_correct (tr : list (name * (raft_input + list raft_output))) : Prop :=
    NoDup (project_input_keys tr).

  Lemma project_input_keys_app :
    forall xs ys,
      project_input_keys (xs ++ ys) = project_input_keys xs ++ project_input_keys ys.
  Proof.
    intros.
    unfold project_input_keys.
    now rewrite filterMap_app.
  Qed.

  Lemma project_input_keys_defn_nil :
    project_input_keys [] = [].
  Proof.
    reflexivity.
  Qed.

  Lemma project_input_keys_defn_cons :
    forall ev tr,
      project_input_keys (ev :: tr) =
      match ev with
        | (_, inl (ClientRequest client id _)) => [ (client, id) ]
        | _ => []
      end ++ project_input_keys tr.
  Proof.
    unfold project_input_keys.
    intros. simpl. repeat break_match; subst; try discriminate; auto.
    find_inversion. auto.
  Qed.

  Lemma input_correct_snoc_inv :
    forall tr ev,
      input_correct (tr ++ [ev]) -> input_correct tr.
  Proof.
    unfold input_correct.
    intros.
    rewrite project_input_keys_app in *.
    rewrite project_input_keys_defn_cons in *.
    rewrite project_input_keys_defn_nil in *.
    repeat break_match; subst; rewrite app_nil_r in *; auto.
    find_apply_lem_hyp NoDup_append.
    solve_by_inversion.
  Qed.
End RaftLinearizableDefinitions.