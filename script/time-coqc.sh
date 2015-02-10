#!/usr/bin/env bash

log=$1
shift

t0=$(date +"%s")
coqc $@
t1=$(date +"%s")

t=$(expr $t1 - $t0)
for last; do true; done
printf "%3d : %s\n" "$t" "$last" >> "$log"
