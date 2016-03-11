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
  echo "proof,lines,words,file,lineno" \
    > "$PROOF_SIZES"
  find ${PADIR}/.. -name '*.v' \
    | xargs ${PADIR}/proof-sizes.awk \
    | sed "s:${PADIR}/../::g" \
    | ${csvsort} --key=2 \
    >> "$PROOF_SIZES"
}

function mkindex {
  cat <<EOF
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Verdi Proofalytics</title>
  <style>
    html {
      font-family: sans-serif;
    }
    body {
      margin: 30px;
    }
    h1 {
      font-size: 28pt;
      color: #4b2e83;
    }
    h2 {
      font-size: 18pt;
      color: #4b2e83;
    }
    p {
      font-size: 14pt;
    }
    .it {
      font-style: italic;
    }
    .bf {
      font-weight: bold;
    }
    .scroller {
      width: 100%;
      height: 400px;
      border: 1px solid #4b2e83;
      overflow: auto;
      margin-bottom: 40px;
    }
    table {
      border-spacing: 10px;
    }
    th {
      text-align: left;
      border-bottom: 1px solid #4b2e83;
    }
  </style>
</head>
<body>
  <h1>Verdi Proofalytics</h1>

  <h2>Proof Sizes</h2>
  <div class='scroller'>
EOF

  cat ${PROOF_SIZES} \
    | awk -f ${PADIR}/proof-sizes-links.awk \
    | awk -f ${PADIR}/csv-table.awk

  cat <<EOF
  </div>
  <h2>Build Times</h2>
  <div class='scroller'>
EOF

  cat ${BUILD_TIMES} \
    | awk -f ${PADIR}/build-times-links.awk \
    | awk -f ${PADIR}/csv-table.awk

  cat <<EOF
  </div>
</body>
</html>
EOF
}

main
