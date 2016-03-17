#!/usr/bin/env bash

cmd=$1
shift

t0=$(date +"%s")
"$cmd" "$@"
status=$?
t1=$(date +"%s")

t=$(expr $t1 - $t0)
for last; do true; done
printf "%s,%d\n" "$last" "$t" > "${last}.buildtime"
exit $status
