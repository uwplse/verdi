verdi
=====

A framework for formally verifying distributed systems implementations in Coq

Building Verdi + case studies
-----------------------------

Requirements:
 - `coq 8.5beta1`

Run `make` in this directory, then run `make` in the `raft/` subdirectory.

Building and running VarD
-------------------------

Requirements:
 - `coq 8.5beta1`
 - `ocaml`, `ocamlbuild`
 - `tmux`

To build and run a vard cluster in debug mode:

    cd extraction/vard
    make
    make debug
  
