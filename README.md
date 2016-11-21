Verdi
=====

[![Build Status](https://api.travis-ci.org/uwplse/verdi.svg?branch=master)](https://travis-ci.org/uwplse/verdi)

A framework for formally verifying distributed systems implementations in Coq.

Requirements
------------

- [`Coq 8.5`](https://coq.inria.fr/download)
- [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/) (`ssreflect` library)
- [`StructTact`](https://github.com/uwplse/StructTact)
- [`InfSeqExt`](https://github.com/DistributedComponents/InfSeqExt)

Building
--------

We recommend installing Coq and `ssreflect` via [OPAM](https://coq.inria.fr/opam/www/using.html).
Be sure to use the package `coq-mathcomp-ssreflect` from the Coq OPAM repository.

Run `./configure` in the Verdi root directory.  This will check
for the appropriate version of Coq and ensure all necessary
dependencies can be located. By default, the script checks for `StructTact`
and `InfSeqExt` in the current parent directory, but this can be 
overridden by setting the `StructTact_PATH` and/or `InfSeqExt_PATH` 
environment variables.

Then run `make` in the Verdi root directory.  This will compile the
specifications and proofs of the core Verdi framework, as well as some
simple example systems and their correctness proofs.

Documentation
-------------

In addition to the example verified systems listed below, see the
scientific papers and blog posts listed at the [Verdi website](http://verdi.uwplse.org).

Files
-----

- Core Verdi files:
    - `Verdi.v`: exporting of core Verdi theories, imported by systems
    - `Net.v`: core (unlabeled) network semantics
    - `LabeledNet.v`: labeled network semantics, for use in liveness reasoning
    - `HandlerMonad.v`: a monad for writing network/input handlers
    - `StatePacketPacket.v`: a technique for writing easily decomposable
    invariants
- Example systems:
    - `Counter.v`: counting server with backup
    - `LockServ.v`: lock server with proof of safety
    - `LiveLockServ.v`: lock server with proof of liveness
    - `VarD.v`: `vard`, a key-value store
- Verified system transformers:
    - `SeqNum.v` and `SeqNumCorrect.v`, a system transformer implementing sequence numbering
        - `LockServSeqNum.v`, the sequence numbering transformer applied to the lock server
    - `PrimaryBackup.v`, a system transformer implementing asynchronous primary-backup replication
        - `VarDPrimaryBackup.v`, the primary-backup transformer applied to the key-value store
- Extraction-related files:
    - `Shim.ml`: OCaml shim for extracted systems verified against a network semantics with _unordered_ message passing, implemented using UDP
    - `OrderedShim.ml`: OCaml shim for extracted systems verified against a network semantics with _ordered_ message passing, implemented using TCP

Projects using Verdi
--------------------

- [`Verdi Raft`](https://github.com/uwplse/verdi-raft): a verified implementation of the Raft distributed consensus protocol
