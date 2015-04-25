default: core systems raft raft-proofs

core: 
	$(MAKE) -C core

systems: core
	$(MAKE) -C systems

raft: core
	$(MAKE) -C raft

raft-proofs: raft
	$(MAKE) -C raft-proofs

clean: 
	$(MAKE) -C core clean
	$(MAKE) -C systems clean
	$(MAKE) -C raft clean
	$(MAKE) -C raft-proofs clean

lint:
	echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

.PHONY: default core systems raft raft-proofs clean lint
