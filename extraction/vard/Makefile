OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

default: vard.native

coq:
	make -C coq

vard.native : coq ml/*.ml lib/*.ml
	$(OCAMLBUILD) vard.native

clean:
	make -C coq clean
	$(OCAMLBUILD) vard.native -clean

clear-data:
	./scripts/clear-verdi.sh

run: vard.native
	./scripts/start-tmux.sh

debug: vard.native
	./scripts/start-tmux-debug.sh

bench-vard: vard.native
	./scripts/bench-vard.sh
	./scripts/clear-verdi.sh

bench-etcd: vard.native
	./scripts/bench-etcd.sh
	./scripts/clear-etcd.sh

.PHONY : default coq run clear-data
