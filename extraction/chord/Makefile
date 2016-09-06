OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

default: chord.native chordshed.native

coq/ExtractedChord.ml:
	# there has to be a -B flag here becuase there's no way to explicitly
	# ask a Makefile.coq for extraction targets
	make -B -C ../../ -f Makefile.coq extraction/chord/coq/ExtractChord.vo

coq/ExtractedChordShed.ml:
	make -B -C ../../ -f Makefile.coq extraction/chord/coq/ExtractChord.vo

chord.native: coq/ExtractedChord.ml ml/*.ml lib/*.ml
	$(OCAMLBUILD) chord.native

chordshed.native: coq/ExtractedChordShed.ml ml/*.ml lib/*.ml
	$(OCAMLBUILD) chordshed.native

clean:
	$(OCAMLBUILD) chord.native -clean

.PHONY : default clean
