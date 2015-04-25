PYTHON=python2.7

default: RaftState.v Makefile.coq
	rm -f ../dash/compile-times-raft.txt
	$(MAKE) -f Makefile.coq

RaftState.v: RaftState.v.rec extract_record_notation.py
	$(PYTHON) extract_record_notation.py RaftState.v.rec raft_data > RaftState.v

Makefile.coq: 
	coq_makefile -R ../core "" -R . "" *.v > Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

.PHONY: Makefile.coq default clean
