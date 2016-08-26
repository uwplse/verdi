Filenames
========

* CamlCase for Coq files, example: `StateMachineHandlerMonad.v`
* CamlCase for OCaml files, example: `VarDArrangement.ml`
* lowercase with dashes for scripts, example: `proof-linter.sh`
* UPPERCASE with underscore for documentation, example: `PROOF_ENGINEERING.md`

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
```
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

```
Instance base_params : BaseParams :=
  {
    data := raft_data ;
    input := raft_input ;
    output := raft_output
  }.
```

Theorems and Lemmas
------

* name uses underscore as separator
* type declaration starts on a separate row
* no unnecessary type declarations for quantified variables
* line break after implication arrow
* proof script indented by two spaces

Example:
```  
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
