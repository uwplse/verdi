#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
STDBUF="$([ -x "$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")"
SEP="__PROOFALYTICS__"
PROOF_TT="${PADIR}/proof-times.ticktock"
PROOF_TIMES="${PADIR}/proof-times.csv"
SANDBOX="$(mktemp -d "/tmp/proofalytics-tmp-XXXXX")"

# initialize sandbox
cp -R "${PADIR}/.." "${SANDBOX}/"

pushd "$SANDBOX" > /dev/null
  # annotate proofs
  for v in $(find . -name '*.v'); do
    scratch="$(mktemp "proot-time-annot-tmp-XXXXX")"
    awk -f "${PADIR}/proof-time-annot.awk" "$v" > "$scratch"
    mv "$scratch" "$v"
  done

  # build
  make clean
  ./configure
  make unbuffered-coqc
  "$STDBUF" -i0 -o0 make \
    | "$STDBUF" -i0 -o0 "${PADIR}/timestamp-lines" \
    > "$PROOF_TT"
popd > /dev/null

# make csv
grep "$SEP" "$PROOF_TT" \
  | sed "s/ /$SEP/" \
  | awk -f "${PADIR}/proof-times-csv.awk" \
  | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
  > "$PROOF_TIMES"

# clean up
rm -rf "$SANDBOX"
