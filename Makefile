PYTHON=python2.7
COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi is only compatible with Coq version 8.5")
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: hacks _CoqProject
	test -s _CoqProject || { echo "Run coqproject.sh before running make"; exit 1; }
	coq_makefile -f _CoqProject -o Makefile.coq

hacks: raft/RaftState.v

raft/RaftState.v:
	$(PYTHON) script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v

clean:
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq

vard: Makefile.coq
	$(MAKE) -f Makefile.coq systems/VarD.vo
	$(MAKE) -f Makefile.coq raft/Raft.vo
	cd extraction/vard; make

lint:
	echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

.PHONY: default clean vard lint hacks
