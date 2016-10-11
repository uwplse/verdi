Verdi
=====

[![Build Status](https://api.travis-ci.org/uwplse/verdi.svg?branch=master)](https://travis-ci.org/uwplse/verdi)

A framework for formally verifying distributed systems implementations in Coq.

Requirements
------------

 - [`Coq 8.5`](https://coq.inria.fr/download)
 - [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/)
 - [`StructTact`](https://github.com/uwplse/StructTact)
 - [`InfSeqExt`](https://github.com/palmskog/InfSeqExt)

Building
--------

First run `./configure` in the Verdi root directory.  This will check
for the appropriate version of Coq and ensure all necessary
dependencies can be located. By default, it checks for `StructTact`
and `InfSeqExt` in the current parent directory, but this can be 
overridden by setting the `StructTact_PATH` and/or `InfSeqExt_PATH` 
environment variables.

Then run `make` in the Verdi root directory.  This will compile the
specifications and proofs of the core Verdi framework, as well as some
simple examples.

Files
-----

- Core Verdi files:
    - `Net.v`: core network semantics
    - `HandlerMonad.v`: a monad for writing network/input handlers
    - `StatePacketPacket.v`: a technique for writing easily decomposable
    invariants
- Example systems:
    - `LockServ.v`: a lock server
    - `VarD.v`: vard, a key-value store
- Verified system transformers:
    - `SeqNum.v` and `SeqNumCorrect.v`, a system transformer
      implementing sequence numbering
      - `LockServSeqNum.v`, the sequence numbering transformer
         applied to the lock server
    - `PrimaryBackup.v`, a system transformer implementing asynchronous
      primary-backup replication
      - `VarDPB.v`, the primary-backup transformer applied to the
        key-value store

Projects using Verdi
--------------------

- [`Verdi Raft`](https://github.com/uwplse/verdi-raft): a verified implementation of the Raft distributed consensus protocol
