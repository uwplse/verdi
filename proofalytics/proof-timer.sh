#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOF_SIZES="${PADIR}/proof-sizes.csv"
BUILD_TIMES="${PADIR}/build-times.csv"
PROOF_TIMES="${PADIR}/proof-times.csv"

STDBUF="$([ -x "$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")"
SANDBOX="$(mktemp -d "/tmp/proofalytics-tmp-XXXXX")"
PROOF_TICKS="${PADIR}/proof-times.ticks"
SEP="__PROOFALYTICS__"

# initialize sandbox
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
  make Makefile.coq
  sed "s:^TIMECMD=\$:TIMECMD=${PADIR}/build-timer.sh $(STDBUF) -i0 -o0:" \
    Makefile.coq > Makefile.coq_tmp
  mv Makefile.coq_tmp Makefile.coq
  "$STDBUF" -i0 -o0 make \
    | "$STDBUF" -i0 -o0 "${PADIR}/timestamp-lines" \
    > "$PROOF_TICKS"

  # proof sizes csv
  find . -name '*.v' \
    | xargs awk -f "${PADIR}/proof-sizes.awk" \
    | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
    > "$PROOF_SIZES"

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
#rm -rf "$SANDBOX"
