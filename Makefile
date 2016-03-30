PYTHON=python2.7
COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi is only compatible with Coq version 8.5")
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

proofalytics:
	$(MAKE) -C proofalytics clean
	$(MAKE) -C proofalytics
	$(MAKE) -C proofalytics publish

STDBUF=$(shell [ -x "$$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")
proofalytics-aux: Makefile.coq
	sed "s|^TIMECMD=$$|TIMECMD=$(PWD)/proofalytics/build-timer.sh $(STDBUF) -i0 -o0|" \
	  Makefile.coq > Makefile.coq_tmp
	mv Makefile.coq_tmp Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: hacks _CoqProject
	test -s _CoqProject || { echo "Run ./configure before running make"; exit 1; }
	coq_makefile -f _CoqProject -o Makefile.coq

hacks: raft/RaftState.v

raft/RaftState.v:
	$(PYTHON) script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq
	find . -name '*.buildtime' -delete
	$(MAKE) -C proofalytics clean

vard:
	@echo "To build everything (including vard) use the default target."
	@echo "To quickly provision vard use the vard-quick target."

vard-quick: Makefile.coq
	$(MAKE) -f Makefile.coq systems/VarD.vo
	$(MAKE) -f Makefile.coq raft/Raft.vo
	$(MAKE) -f Makefile.coq extraction/vard/coq/ExtractVarDRaft.vo
	cd extraction/vard; make

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default clean vard vard-quick lint hacks proofalytics distclean
