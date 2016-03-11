#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUILD_TIMES="${PADIR}/build-times.csv"
PROOF_SIZES="${PADIR}/proof-sizes.csv"
INDEX="${PADIR}/index.html"

function main {
  build-times
  proof-sizes
  mkindex > "$INDEX"
}

# making this a function doesn't work w/ xargs :\
csvsort="sort --field-separator=, --numeric-sort --reverse"

function build-times {
  echo "file,time" > "$BUILD_TIMES"
  find ${PADIR}/.. -name '*.buildtime' \
    | xargs ${csvsort} --key=2 \
    >> "$BUILD_TIMES"
}

function proof-sizes {
  echo "file,proof,lines,words,chars" \
    > "$PROOF_SIZES"
  find ${PADIR}/.. -name '*.v' \
    | xargs ${PADIR}/proof-sizes.awk \
    | sed "s:${PADIR}/../::g" \
    | ${csvsort} --key=3 \
    >> "$PROOF_SIZES"
}

function mkindex {
  cat <<EOF
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Verdi Proofalytics</title>
  <link rel='stylesheet' type='text/css' href='style.css'>
</head>
<body>
  <h1>Verdi Proofalytics</h1>
</body>
</html>
EOF
}

main
