#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUILD_TIMES="${PADIR}/build-times.csv"
PROOF_SIZES="${PADIR}/proof-sizes.csv"

function main {
  build-times
  proof-sizes
}

# making this a function doesn't work w/ xargs :\
csvsort="sort --field-separator=, --numeric-sort --reverse"

function build-times {
  find ${PADIR}/.. -name '*.buildtime' \
    | xargs ${csvsort} --key=2 \
    > "$BUILD_TIMES"
}

function proof-sizes {
  find ${PADIR}/.. -name '*.v' \
    | xargs ${PADIR}/proof-sizes.awk \
    | sed "s:${PADIR}/../::g" \
    | ${csvsort} --key=3 \
    > "$PROOF_SIZES"
}

main
