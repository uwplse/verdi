Verdi
=====

[![Build Status](https://api.travis-ci.org/uwplse/verdi.svg?branch=master)](https://travis-ci.org/uwplse/verdi)

A framework for formally verifying distributed systems implementations in Coq.

Requirements
------------

Framework:

- [`Coq 8.5`](https://coq.inria.fr/coq-85) or [`Coq 8.6`](https://coq.inria.fr/coq-86)
- [`mathcomp-ssreflect 1.6`](http://math-comp.github.io/math-comp/) or [`mathcomp-ssreflect 1.6.1`](http://math-comp.github.io/math-comp/)
- [`StructTact`](https://github.com/uwplse/StructTact)
- [`InfSeqExt`](https://github.com/DistributedComponents/InfSeqExt)

Runtime:

- [`OCaml 4.02.3`](https://ocaml.org/docs/install.html) (or later)
- [`verdi-runtime`](https://github.com/DistributedComponents/verdi-runtime)

Building
--------

We recommend installing Verdi via [OPAM](http://opam.ocaml.org/doc/Install.html),
which will automatically build and install its dependencies.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install verdi
```

To build Verdi manually, it is a good idea to first consult the [`opam`](opam)
file for exact requirements.

Then, run `./configure` in the Verdi root directory.  This will check
for the appropriate version of Coq and ensure all necessary
dependencies can be located. By default, the script assumes that `StructTact`
and `InfSeqExt` are installed in Coq's `user-contrib` directory, but this
can be overridden by setting the `StructTact_PATH` and/or `InfSeqExt_PATH`
environment variables.

Finally, run `make` in the Verdi root directory.  This will compile the
framework's core specifications and proofs, as well as some
simple example systems and their correctness proofs.

Runtime Library
---------------

To run Verdi systems on real hardware, event handler code must be extracted
to OCaml and linked with one of the shims in the Verdi
[runtime library](https://github.com/DistributedComponents/verdi-runtime)
that handles low-level network communication.

To install the runtime library via OPAM, make sure the `distributedcomponents-dev`
repo has been added as above and use the following command:

```
opam install verdi-runtime
```

Getting Started
---------------

To set up your own Verdi-based distributed systems verification project, we recommend
forking [Verdi LockServ](https://github.com/DistributedComponents/verdi-lockserv).

Verdi LockServ contains a minimalistic implementation of a message-passing lock server
and a proof that it maintains mutual exclusion between client nodes. At build time,
extracted OCaml code is linked to a runtime library shim to produce an executable
program that can be run in a cluster. There is also a simple script to interface
with cluster nodes.

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

Projects using Verdi
--------------------

- [`Verdi Raft`](https://github.com/uwplse/verdi-raft): a verified implementation of the Raft distributed consensus protocol
