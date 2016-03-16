#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

SYNC="rsync --exclude '.*' --chmod=ug=rwX --chmod=o=rX --recursive"
WEB_MACH="uwplse.org"
WEB_PATH="/var/www/verdi/dash/"
RDASH="${WEB_MACH}:${WEB_PATH}"
LDASH="${PADIR}/dash/"
NONCE=$(printf "PA-%s-%s-%s-%s" \
               $(date "+%y%m%d") \
               $(date "+%H%M%S") \
               $(hostname -s) \
               $(git rev-parse --abbrev-ref HEAD))
REPDIR="${LDASH}${NONCE}"

function main {
  echo "SYNC remote -> local"
  $SYNC "$RDASH" "$LDASH"

  mkdir "$REPDIR"
  cp index.html *.csv "$REPDIR"

  mkindex > "${LDASH}index.html"

  echo "SYNC local  -> remote"
  $SYNC "$LDASH" "$RDASH"
}

function mkindex {
  pushd "$LDASH" > /dev/null

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
    ul {
      list-style-type: square;
    }
    li {
      padding-bottom: 10px;
      line-height: 150%;
    }
  </style>
</head>
<body>
  <h1>Verdi Proofalytics</h1>
  <ul>
EOF
  for rep in $(ls -r | grep 'PA-*'); do
    echo "<li>"

    printf "<a href='%s'>%s</a>\n" "$rep" "$rep"

    echo "<br> &nbsp;"
    echo "<span class='it'>max ltac:</span> &nbsp;"
    cat "${rep}/proof-times.csv" \
      | awk -v key=2 -f "${PADIR}/csv-sort.awk" \
      | awk -F "," 'NR == 2 {print $1 " (" $2 " ms)"}'

    echo "<br> &nbsp;"
    echo "<span class='it'>max qed:</span> &nbsp;"
    cat "${rep}/proof-times.csv" \
      | awk -v key=3 -f "${PADIR}/csv-sort.awk" \
      | awk -F "," 'NR == 2 {print $1 " (" $2 " ms)"}'

    echo "<br> &nbsp;"
    echo "<span class='it'>build time:</span> &nbsp;"
    awk 'BEGIN { FS = ","; tot = 0 }  \
         { tot += $2 }      \
         END { print tot " s"}' \
        "${rep}/build-times.csv"

    # TODO
    # echo "<br> &nbsp;"
    # echo "<span class='it'>admits:</span> &nbsp;"

    echo "</li>"
  done
  cat <<EOF
  </ul>
</body>
</html>
EOF
  popd > /dev/null
}

main
