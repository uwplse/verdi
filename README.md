# Verdi

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/uwplse/verdi/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/uwplse/verdi/actions?query=workflow:"Docker%20CI"




Verdi is a Coq framework to implement and formally verify distributed systems.
Verdi supports several different fault models ranging from idealistic to realistic.
Verdi's verified system transformers (VSTs) encapsulate common fault tolerance
techniques. Developers can verify an application in an idealized fault model, and
then apply a VST to obtain an application that is guaranteed to have analogous
properties in a more adversarial environment.

## Meta

- Author(s):
  - Justin Adsuara
  - Steve Anton
  - Ryan Doenges
  - Karl Palmskog
  - Pavel Panchekha
  - Zachary Tatlock
  - James R. Wilcox
  - Doug Woos
- License: [BSD 2-Clause "Simplified" license](LICENSE)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [InfSeqExt](https://github.com/DistributedComponents/InfSeqExt)
  - [StructTact](https://github.com/uwplse/StructTact)
  - [Cheerios](https://github.com/uwplse/cheerios)
- Coq namespace: `Verdi`
- Related publication(s):
  - [Verdi: A Framework for Implementing and Verifying Distributed Systems](http://verdi.uwplse.org/verdi.pdf) doi:[10.1145/2737924.2737958](https://doi.org/10.1145/2737924.2737958)
  - [Planning for Change in a Formal Verification of the Raft Consensus Protocol](http://verdi.uwplse.org/raft-proof.pdf) doi:[10.1145/2854065.2854081](https://doi.org/10.1145/2854065.2854081)

## Building and installation instructions

We recommend installing Verdi via [opam](http://opam.ocaml.org/doc/Install.html),
which will automatically build and install its dependencies:
```shell
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-verdi
```

To build Verdi manually, first install all requirements. Then,
run `make` in the Verdi root directory.  This will compile
the framework's core specifications and proofs, as well as some
simple example systems and their correctness proofs.

To run Verdi systems on real hardware, event handler code must be extracted
to OCaml and linked with one of the shims in the Verdi
[runtime library](https://github.com/DistributedComponents/verdi-runtime)
that handles low-level network communication.

## Documentation

To set up your own Verdi-based distributed systems verification project, we
recommend basing it on
[Verdi LockServ](https://github.com/DistributedComponents/verdi-lockserv).

Verdi LockServ contains a minimalistic implementation of a message-passing
lock server and a proof that it maintains mutual exclusion between client
nodes. At build time, extracted OCaml code is linked to a runtime library
shim to produce an executable program that can be run in a cluster. There
is also a simple script to interface with cluster nodes.

In addition to the example verified systems listed below, see the
scientific papers and blog posts listed at the
[Verdi website](http://verdi.uwplse.org). See also
[Verdi Raft](https://github.com/uwplse/verdi-raft), a verified
implementation of the Raft distributed consensus protocol.

### Files

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
