default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -Q ../.. "" -Q .. "" -Q . "" -arg -no-native-compiler *.v > Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq

.PHONY: Makefile.coq
