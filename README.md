Verdi
=====

[![Build Status](https://api.travis-ci.org/uwplse/verdi.svg?branch=master)](https://travis-ci.org/uwplse/verdi)

A framework for formally verifying distributed systems implementations in Coq

The Verdi Framework
-------------------

Requirements:

 - `coq 8.5beta1`

Running `make` in the root directory will compile the specifications
and proofs of the core Verdi framework, as well as some simple
examples. The files in the root directory include:

- Core Verdi files:
    - `Net.v`: core network semantics, including ghost variables
    - `VerdiTactics.v` and `Util.v`, tactics and lemmas for Verdi proofs
    - `HandlerMonad.v`: a monad for writing network/input handlers
    - `StatePacketPacket.v`: a technique for writing easily decomposable
    invariants
- Example systems
    - `LockServ.v`: a lock server
    - `VarD.v`: vard, a key-value store
- Verified system transformers
    - `SeqNum.v` and `SeqNumCorrect.v`, a system transformer
      implementing sequence numbering
    - `PrimaryBackup.v`, a system transformer implementing asynchronous
      primary-backup replication
      - `VarDPB.v`, the primary-backup transformer applied to the
        key-value store

The Raft Consensus Protocol
---------------------------

The `raft` subdirectory contains an implementation and partial
verification of the Raft distributed consensus protocol. After
building Verdi, running `make` in the `raft` subdirectory will compile
the Raft implementation and proofs. The files in the Raft subdirectory
include:

- `Raft.v`: an implementation of Raft in Verdi
- `RaftRefinement.v`: an application of the ghost-variable transformer
  to Raft which tracks several ghost variables used in the
  verification of Raft
- `CommonTheorems.v`: several useful theorems about functions used by
  the Raft implementation
- `OneLeaderPerTerm`: a statement and proof of Raft's **Election
  safety** property
  - `CandidatesVoteForSelves.v`, `VotesCorrect.v`, and
    `CroniesCorrect.v`: statements and proofs of properties used by
    `OneLeaderPerTerm.v`
- `LogMatching.v`: a statement and proof of Raft's *Log Matching*
    property
  - `LeaderSublog.v`, `Sorted.v`, and `UniqueIndices.v`: statements
    and proofs of properties used by `LogMatching.v`

The vard Key-Value Store
------------------------

Requirements:

- `coq 8.5beta1`
- `ocaml`, `ocamlbuild`

As discussed above, vard is a simple key-value store implemented in
Verdi. vard is specified and verified against Verdi's state-machine
semantics in `VarD.v`. When the Raft transformer is applied, `vard`
can be run as a strongly-consistent, fault-tolerant key-value store
along the lines of etcd. The Coq and Ocaml files necessary to run vard
on real hardware are in `extraction/vard`. Running `make` in that
directory will extract the vard and Raft code, link it against the
Verdi shim and some vard-specific serialization/debugging code, and
compile it all into a `vard.native` binary. Running `make bench-vard`
will produce some benchmark numbers, which are largely meaningless on
localhost (multiple processes writing and fsync-ing to the same disk
and communicating over loopback doesn't accurately model real-world
use cases). Running `make debug` will get you a `tmux` session where
you can play around with a vard cluster in debug mode; look in
`bench/vard.py` for a simple python `vard` client.

As the name suggests, vard is designed to be comparable to the etcd
key-value store (although it currently supports many fewer
features). To that end, we include a very simple etcd "client" which
can be used for benchmarking. Running `make bench-etcd` will run the
vard benchmarks against etcd (although see above for why these results
are not particularly meaningful). See below for instructions to run
both stores on a cluster in order to get a more useful performance
comparison.

Running vard on a cluster
-------------------------

vard doesn't support run-time configuration, so in order to run vard
in another configuration (i.e. on multiple hosts) you'll have to edit
the `extraction/vard/vard.ml` file, specifically the 4 lines starting
with `let nodes = ...`. For instance, to run it on a cluster with ip
addresses `192.168.0.1, 192.168.0.2, 192.168.0.3` you'd edit those
lines to read

    let nodes = [ (1, ("192.168.0.1", 9001))
                ; (2, ("192.168.0.2", 9001))
                ; (3, ("192.168.0.3", 9001))
                ]

The port is the port used for internal communication; the client port
is hard-coded to be `internal-port - 1000` (8001 in this
example). After recompiling with this config, you could run the
benchmarks on a cluster as follows:

    # on 192.168.0.1
    $ ./vard.native 1

    # on 192.168.0.2
    $ ./vard.native 2
    
    # on 192.168.0.3
    $ ./vard.native 3

    # on the client machine
    $ python2 bench/setup.py --service vard --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001"
    $ python2 bench/bench.py --service vard --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001" \
                             --threads 8 --requests 100


Running etcd on a cluster
-------------------------

We can compare vard's numbers to etcd running on the same cluster as
follows:

    # on 192.168.0.1
    $ etcd --name=one \
     --listen-client-urls http://192.168.0.1:8001 \
     --advertise-client-urls http://192.168.0.1:8001 \
     --initial-advertise-peer-urls http://192.168.0.1:9001 \
     --listen-peer-urls http://192.168.0.1:9001 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9001,two=http://192.168.0.2:9001,three=http://192.168.0.3:9001"

    # on 192.168.0.2
    $ etcd --name=two \
     --listen-client-urls http://192.168.0.2:8001 \
     --advertise-client-urls http://192.168.0.2:8001 \
     --initial-advertise-peer-urls http://192.168.0.2:9001 \
     --listen-peer-urls http://192.168.0.2:9001 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9001,two=http://192.168.0.2:9001,three=http://192.168.0.3:9001"

    # on 192.168.0.3
    $ etcd --name=three \
     --listen-client-urls http://192.168.0.3:8001 \
     --advertise-client-urls http://192.168.0.3:8001 \
     --initial-advertise-peer-urls http://192.168.0.3:9001 \
     --listen-peer-urls http://192.168.0.3:9001 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9001,two=http://192.168.0.2:9001,three=http://192.168.0.3:9001"

    # on the client machine
    $ python2 bench/setup.py --service etcd --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001"
    $ python2 bench/bench.py --service etcd --keys 50 \
                             --cluster "192.168.0.1:8001,192.168.0.2:8001,192.168.0.3:8001" \
                             --threads 8 --requests 100
