LIBS=

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	LIBS+= -lrt
endif

proofalytics: timestamp-lines
	./proof-linter.sh
	./proof-timer.sh
	./mkreport.sh

timestamp-lines: timestamp-lines.c
	gcc $< -o $@ $(LIBS)

publish:
	./publish.sh

clean:
	rm -f build-times.csv proof-sizes.csv
	rm -f proof-times.csv proof-times.ticks
	rm -f index.html
	rm -f timestamp-lines

.PHONY: proofalytics publish clean
