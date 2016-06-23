OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

default: chord.native

coq:
	make -C coq

chord.native : coq ml/*.ml lib/*.ml
	$(OCAMLBUILD) chord.native

clean:
	make -C coq clean
	$(OCAMLBUILD) chord.native -clean

.PHONY : default coq
