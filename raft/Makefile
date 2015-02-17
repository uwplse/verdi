PYTHON=python2.7

default: RaftState.v Makefile.coq
	rm -f ../dash/compile-times-raft.txt
	$(MAKE) -f Makefile.coq

RaftState.v: RaftState.v.rec extract_record_notation.py
	$(PYTHON) extract_record_notation.py RaftState.v.rec raft_data > RaftState.v

Makefile.coq:
	coq_makefile -Q .. "" -Q . "" -arg -no-native-compiler *.v > Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq
