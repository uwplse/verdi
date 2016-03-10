PYTHON=python2.7
COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi is only compatible with Coq version 8.5")
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq
	$(PWD)/script/proofalytics.sh

Makefile.coq: hacks _CoqProject
	test -s _CoqProject || { echo "Run ./configure before running make"; exit 1; }
	coq_makefile -f _CoqProject -o Makefile.coq
	sed -i 's:^TIMECMD=$$:TIMECMD=$(PWD)/script/build-timer.sh:' Makefile.coq

hacks: raft/RaftState.v

raft/RaftState.v:
	$(PYTHON) script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq build-times.csv
	find . -name '*.buildtime' -delete

vard: Makefile.coq
	$(MAKE) -f Makefile.coq systems/VarD.vo
	$(MAKE) -f Makefile.coq raft/Raft.vo
	cd extraction/vard; make

lint:
	echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

.PHONY: default clean vard lint hacks
