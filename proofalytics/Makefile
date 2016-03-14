WEB_MACH=uwplse.org
WEB_PATH=/var/www/verdi/dash

proofalytics: timestamp-lines
	./proofalytics.sh

timestamp-lines: timestamp-lines.c
	gcc $< -o $@

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
