#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
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
  make \
    | grep '__PROOFALYTICS__' \
    | "${PADIR}/timestamp-lines" \
    > "$PROOF_TT"
popd > /dev/null

# make csv
echo "proof,ltac,qed,file,lineno" > "$PROOF_TIMES"
awk -f "${PADIR}/proof-times-csv.awk" "$PROOF_TT" \
  | sort --field-separator=, \
         --numeric-sort \
         --reverse \
         --key=2 \
  >> "$PROOF_TIMES"

# clean up
rm -rf "$SANDBOX"
