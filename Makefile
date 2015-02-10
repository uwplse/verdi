
default: Makefile.coq
	rm -f dash/compile-times.txt
	$(MAKE) -f Makefile.coq

raft:
	$(MAKE) -C raft

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq

dash:
	cd dash/ && $(MAKE)

Makefile.coq:
	coq_makefile -Q . "" *.v > Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

doc:
	pandoc -s -c doc/style.css doc/overview.md -o doc/overview.html

lint:
	echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

.PHONY: default clean doc raft dash lint

