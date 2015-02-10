default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -Q ../../.. "" -Q ../../../raft "" -Q . "" *.v > Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f *.ml *.mli
	rm -rf Makefile.coq
