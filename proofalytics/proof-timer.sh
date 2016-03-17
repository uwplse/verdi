#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUILD_TIMES="${PADIR}/build-times.csv"
PROOF_TIMES="${PADIR}/proof-times.csv"
PROOF_TICKS="${PADIR}/proof-times.ticks"

STDBUF="$([ -x "$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")"
SEP="__PROOFALYTICS__"

# initialize sandbox, must be sibling of verdi root
SANDBOX="$(mktemp -d "${PADIR}/../../proofalytics-tmp-XXXXX")"
cp -R "${PADIR}/.." "${SANDBOX}/"

pushd "$SANDBOX" > /dev/null
  # annotate proofs
  for v in $(find . -name '*.v'); do
    scratch="$(mktemp "proot-time-annot-tmp-XXXXX")"
    awk -f "${PADIR}/proof-time-annot.awk" "$v" > "$scratch"
    mv "$scratch" "$v"
  done

  # build w/ timing and no buffers
  make clean
  ./configure
  "$STDBUF" -i0 -o0 make proofalytics-aux \
    | "$STDBUF" -i0 -o0 "${PADIR}/timestamp-lines" \
    > "$PROOF_TICKS"

  # build times csv
  echo "file,time" \
    | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
      - $(find . -name '*.buildtime') \
    > "$BUILD_TIMES"

  # proof times csv
  grep "$SEP" "$PROOF_TICKS" \
    | sed "s/ /$SEP/" \
    | awk -f "${PADIR}/proof-times-csv.awk" \
    | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
    > "$PROOF_TIMES"
popd > /dev/null

# clean up
rm -rf "$SANDBOX"
