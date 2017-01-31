Filenames
========

* CamlCase for Coq files, example: `StateMachineHandlerMonad.v`
* CamlCase for OCaml files, example: `VarDArrangement.ml`
* lowercase with dashes for scripts, example: `proof-linter.sh`
* UPPERCASE with underscores for documentation, example: `PROOF_ENGINEERING.md`

Coq Files
=========

Sections
--------

* CamlCase name, example: `Section StepRelations.`
* indentation of two spaces for all code inside a section

Type Classes
------------

* CamlCase name
* brackets on separate line indented by two spaces
* field declaration with C-style naming on separate line indented by four spaces
* one space between end of field declaration and semicolon

Example:
```coq
Class GhostFailureParams `(P : FailureParams) :=
  {
    ghost_data : Type;
    ghost_init : ghost_data ;
    ghost_net_handlers :
      name -> name -> msg -> (ghost_data * data) -> ghost_data ;
    ghost_input_handlers :
      name -> input -> (ghost_data * data) -> ghost_data
  }.
```

Type Class Instances
--------------------

* C-style names
* brackets on separate line indented by two spaces
* field declaration with C-style naming on separate line indented by four spaces
* one space between end of field declaration and semicolon

Example:
```coq
Instance base_params : BaseParams :=
  {
    data := raft_data ;
    input := raft_input ;
    output := raft_output
  }.
```

Theorems and Lemmas
-------------------

* name uses underscore as separator
* type declaration starts on a separate row
* no unnecessary type declarations for quantified variables
* line break after implication arrow
* proof script indented by two spaces

Example:
```coq
Theorem inverse_trace_relations_work :
  forall s tr,
    refl_trans_1n_trace step init s tr ->
    R s ->
    T tr.
Proof.
  intros. find_apply_lem_hyp refl_trans_1n_n1_trace.
  remember init as s'.
  induction H.
  - subst. exfalso. eauto using R_false_init.
  - subst. concludes.
    destruct (R_dec x');
      intuition eauto using T_monotonic, refl_trans_n1_1n_trace, R_implies_T.
Qed.
```

Step Relation Definitions
-------------------------

* C-style name of (`Inductive`) type
* each case starts with a bar
* name of a case is the type name in CamelCase, followed by an underscore and a C-style identifier
* body of a case is indented by four spaces

Example:
```coq
Inductive step_async : step_relation network (name * (input + list output)) :=
| StepAsync_deliver : forall net net' p xs ys out d l,
    nwPackets net = xs ++ p :: ys ->
    net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
    net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                     (update name_eq_dec (nwState net) (pDst p) d) ->
    step_async net net' [(pDst p, inr out)]
| StepAsync_input : forall h net net' out inp d l,
    input_handlers h inp (nwState net h) = (out, d, l) ->
    net' = mkNetwork (send_packets h l ++ nwPackets net)
                     (update name_eq_dec (nwState net) h d) ->
    step_async net net' [(h, inl inp); (h, inr out)].
```
