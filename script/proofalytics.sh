#!/usr/bin/env bash

set -e

VERDI_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUILD_TIMES="${VERDI_SCRIPT}/../build-times.csv"
PROOF_SIZES="${VERDI_SCRIPT}/../proof-sizes.csv"

function main {
  build-times
  proof-sizes
}

# making this a function doesn't work w/ xargs :\
csvsort="sort --field-separator=, --numeric-sort --reverse"

function build-times {
  find ${VERDI_SCRIPT}/.. -name '*.buildtime' \
    | xargs ${csvsort} --key=2 \
    > "$BUILD_TIMES"
}

function proof-sizes {
  find ${VERDI_SCRIPT}/.. -name '*.v' \
    | xargs ${VERDI_SCRIPT}/proof-sizes.awk \
    | sed "s:${VERDI_SCRIPT}/../::g" \
    | ${csvsort} --key=3 \
    > "$PROOF_SIZES"
}

main
