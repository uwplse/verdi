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

.PHONY: proofalytics clean publish
