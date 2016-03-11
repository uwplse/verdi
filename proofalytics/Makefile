WEB_MACH=uwplse.org
WEB_PATH=/var/www/verdi/dash

proofalytics:
	./proofalytics.sh

publish:
	rsync \
	  --exclude '.*' \
	  --chmod=ug=rwX \
	  --recursive . "$(WEB_MACH):$(WEB_PATH)"

clean:
	rm -f build-times.csv proof-sizes.csv

.PHONY: proofalytics clean publish
