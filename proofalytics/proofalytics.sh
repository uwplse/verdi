#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOF_SIZES="${PADIR}/proof-sizes.csv"
PROOF_TIMES="${PADIR}/proof-times.csv"
BUILD_TIMES="${PADIR}/build-times.csv"
INDEX="${PADIR}/index.html"

COMMIT="$(git rev-parse HEAD)"

function main {
  proof-sizes
  build-times
  mkindex > "$INDEX"
}

function proof-sizes {
  find ${PADIR}/.. -name '*.v' \
    | xargs awk -f "${PADIR}/proof-sizes.awk" \
    | sed "s:${PADIR}/../::g" \
    | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
    > "$PROOF_SIZES"
}

function build-times {
  echo "file,time" \
    | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
      - $(find ${PADIR}/.. -name '*.buildtime') \
    > "$BUILD_TIMES"
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
      width: 98%;
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
      color: #4b2e83;
      border-bottom: 1px solid #4b2e83;
    }
    #cfg {
      margin-bottom: 40px;
    }
    .cfg-fld {
      color: #4b2e83;
      font-weight: bold;
      padding-right: 10px;
    }
  </style>
</head>
<body>
  <h1>Verdi Proofalytics</h1>
  <h2>Configuration</h2>
  <table id='cfg'><tr>
    <td class='cfg-fld'>Date</td>
    <td>$(date)</td>
  </tr><tr>
    <td class='cfg-fld'>Host</td>
    <td>$(whoami)@$(hostname -s)</td>
  </tr><tr>
    <td class='cfg-fld'>Commit</td>
    <td>
      <a href='https://github.com/uwplse/verdi/commit/$COMMIT'>
      $COMMIT</a>
    </td>
  </tr></table>
EOF
  if [ -f "$PROOF_SIZES" ]; then
    echo "<h2>Proof Sizes</h2>"
    echo "<div class='scroller'>"
    cat "$PROOF_SIZES" \
      | awk -v commit="$COMMIT" \
            -f "${PADIR}/proof-sizes-links.awk" \
      | awk -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi
  if [ -f "$BUILD_TIMES" ]; then
    echo "<h2>Build Times</h2>"
    echo "<div class='scroller'>"
    cat "$BUILD_TIMES" \
      | awk -v commit="$COMMIT" \
            -f "${PADIR}/build-times-links.awk" \
      | awk -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi
  if [ -f "$PROOF_TIMES" ]; then
    echo "<h2>Proof Times</h2>"
    echo "<div class='scroller'>"
    cat "$PROOF_TIMES" \
      | awk -v commit="$COMMIT" \
            -f "${PADIR}/proof-times-links.awk" \
      | awk -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi
  cat <<EOF
</body>
</html>
EOF
}

main
