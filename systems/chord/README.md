Quick start
-----------
Run `python2 demo.py | python2 report.py | grep -v DEBUG` and watch the `f`s
turn into `t`s. If you're not using Linux you probably have to bring more
localhost IPs up before this will work: see the bottom of the "Running it"
section for how to fix that.

Introduction
============
This is an implementation of Pamela Zave's [correct specification][1] of Chord
written in Python as preparation for a formal model in Coq. To this end, the
code is structured into handlers to match the network semantics in
DynamicNet.v, and accompanied with a tool for detecting violations of the
inductive invariant presented in Zave's paper.

Any design limitations in the Zave specification also apply to this
implementation. For example, there's no key-value storage or external API
available in this implementation, since Zave's paper doesn't include anything
to that end. 

Running it
==========
Presently the only available command just runs a demo, in which a ring of nodes
is started up and then a few of them are killed off. This is an artifact of the
code's general disorganization, and when I fix that I'll be sure to get the
demo separated from the chord implementation itself. 

That said, the demo is pretty satisfying to watch. As mentioned above, running
`python2 demo.py | python2 report.py` will get it going. Grepping out all the
`DEBUG` lines will make the output far less noisy but is, of course, unwise if
you're trying to debug anything.

The demo in `demo.py` creates an ideal Chord ring composed of 40 subprocesses
running Chord nodes. The ring is ideal because each Chord node is initialized
with globally correct successor lists and predecessor pointers. The processes
communicate using TCP over the localhost IP network. Once all those processes
are up and running, the original process terminates two of them (causing two
node failures) and shortly afterward adds another node with the join protocol.
The remaining nodes will restore the ring to an ideal state, so that eventually
the demo hosts an ideal Chord ring of 39 nodes.

Note that on OS X, 127.0.0.1 seems to be the only address set up as a
loopback address by default (as opposed to the whole 127.0.0.0/8
subnet as on Linux). The chord demo relies on multiple addresses in
127.0.0.0/24, so before running it on OS X you'll need to do the
following:

```
for ((i=2;i<256;i++))
do
    sudo ifconfig lo0 alias 127.0.0.$i up
done
```

Understanding the output of the demo
====================================
The code in `demo.py` logs any changes to node state, including predecessor
pointers and successor pointers. The checker in `report.py` parses out these
changes from the logs.

After each logged line, the checker, well, checks. With the new information
from the logged line incorporated into its global node data, the checker prints
out a summary of which of Zave's invariants are currently holding and whether
the ring is ideal. Here's a sample run, with some of the initialization
messages replaced with an ellipse and all of the debug log messages hidden.

```
at_least_one_ring
| at_most_one_ring
| | ordered_ring
| | | connected_appendages
| | | | ordered_successor_lists
| | | | | globally_correct_node_data
| | | | | | ideal_ring
| | | | | | |
| | | | | | |	INFO:__main__(21):id := 21
...
| | | | | | |	INFO:__main__(1995):id := 1995
t t t t t f t	INFO:__main__(1995):id := 1995
t t t t t f t	INFO:__main__(1995):succ_list := [21, 78, 83]
t t t t t t t	INFO:__main__(1995):joined := True
t t t t t f t	WARNING:root:killing node 105
t t t t t f t	WARNING:root:killing node 322
t t t t t f t	INFO:__main__(140):succ_list := [416, 478]
t t t t t f t	INFO:__main__(83):succ_list := [140, 322]
t t t t t f t	INFO:__main__(83):succ_list := [140, 416, 478]
t t t t t f t	INFO:__main__(140):succ_list := [416, 478, 515]
t t t t t f t	INFO:__main__(83):succ_list := [140, 322]
t t t t t f t	INFO:__main__(78):succ_list := [83, 140, 416]
t t t t t f t	INFO:__main__(140):succ_list := [416, 478]
t t t t t f t	INFO:__main__(21):succ_list := [78, 83, 140]
t t t t t f t	INFO:__main__(83):succ_list := [140, 416, 478]
t t t t t f t	INFO:__main__(140):pred := None
t t t t t f t	INFO:__main__(140):pred := 83
t t t t t f t	INFO:__main__(140):succ_list := [416, 478, 515]
t t t t t f t	INFO:__main__(416):pred := None
t t t t t t t	INFO:__main__(416):pred := 140
t t t t t f t	INFO:__main__(83):succ_list := [140, 322]
t t t t t t t	INFO:__main__(83):succ_list := [140, 416, 478]
t t t t t f t	INFO:__main__(140):succ_list := [416, 478]
t t t t t t t	INFO:__main__(140):succ_list := [416, 478, 515]
```

Each line, after the header, consists of a series of `t`s or `f`s (for "true"
or "false") followed by a log message. The first messages will be prefixed with
pipe characters until all of Zave's invariants hold, so as to avoid the
confusion that could result from checking for invariants on half the log
messages from the initialized ring.

Listed in the header are some properties of the global Chord state. The first
four are actually Zave's invariants. I have omitted Zave's "stable base"
invariant because it would require specifying the stable base ahead of time,
but I'll add it eventually. I have also added `ordered_successor_lists`, one of
Zave's "candidate invariants" that in conjunction with the first four
properties is not actually strong enough to serve as an inductive invariant for
Chord, but is entailed by the "stable base" invariant. For more details on
this, consult [the paper][1].

The last two properties, `globally_correct_node_data` and `ideal_ring`, are not
invariant properties of Chord. They only describe ideal network states. If this
implementation is correct, the network should eventually be able to make these
two properties of the ring true given enough time without node failures or new
joins.

Each line is prefixed with the properties true of the network immediately after
the line was logged. The last two columns can be "f", but if any of the other
ones aren't true then some invariant has been violated and there's something
wrong with the implementation.

1: http://arxiv.org/abs/1502.06461v2
