WEB_MACH=uwplse.org
WEB_PATH=/var/www/verdi/dash

LIBS=

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	LIBS+= -lrt
endif

proofalytics: timestamp-lines
	./proofalytics.sh

timestamp-lines: timestamp-lines.c
	gcc $< -o $@ $(LIBS)

publish:
	rsync \
	  --exclude '.*' \
	  --chmod=ug=rwX \
	  --recursive . "$(WEB_MACH):$(WEB_PATH)"

clean:
	rm -f build-times.csv proof-sizes.csv
	rm -f proof-times.csv proof-times.ticktock
	rm -f timestamp-lines

.PHONY: proofalytics clean publish
