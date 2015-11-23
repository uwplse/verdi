COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi is only compatible with Coq version 8.5")
endif

default: core lib systems raft raft-proofs

core: 
	$(MAKE) -C core

lib: core
	$(MAKE) -C lib

systems: core lib
	$(MAKE) -C systems

raft: core
	$(MAKE) -C raft

raft-proofs: raft
	$(MAKE) -C raft-proofs

clean: 
	$(MAKE) -C lib clean
	$(MAKE) -C core clean
	$(MAKE) -C systems clean
	$(MAKE) -C raft clean
	$(MAKE) -C raft-proofs clean

vard: core lib
	cd systems; make Makefile.coq; make -f Makefile.coq VarD.vo
	cd raft; make Makefile.coq; make -f Makefile.coq Raft.vo
	cd extraction/vard; make

lint:
	echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

.PHONY: default lib core systems raft raft-proofs clean lint vard
