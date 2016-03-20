#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

SYNC="rsync --exclude '.*' --chmod=ug=rwX --chmod=o=rX --recursive"
WEB_MACH="uwplse.org"
WEB_PATH="/var/www/verdi/dash/"
RDASH="${WEB_MACH}:${WEB_PATH}"
LDASH="${PADIR}/dash/"
HOST="$([ "$TRAVIS_BRANCH" != "" ] && \
          echo "travis" || \
          hostname -s)"
BRANCH="$([ "$TRAVIS_BRANCH" != "" ] && \
            echo "$TRAVIS_BRANCH" || \
            git rev-parse --abbrev-ref HEAD)"
NONCE=$(printf "PA-%s-%s-%s-%s" \
               $(TZ="America/Los_Angeles" date "+%y%m%d") \
               $(TZ="America/Los_Angeles" date "+%H%M%S") \
               "$HOST" \
               "$BRANCH")
REPDIR="${LDASH}${NONCE}"

function main {
  echo "SYNC remote -> local"
  $SYNC "$RDASH" "$LDASH"

  mkdir "$REPDIR"
  cp index.html admit-count.txt *.csv "$REPDIR"
  # publish ticks for debugging travis ci
  cp *.ticks "$REPDIR"

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
    .pa-link {
      text-decoration: none;
    }
    .pa-link:hover {
      font-style: italic;
    }
  </style>
</head>
<body>
  <h1>Verdi Proofalytics</h1>
  <ul>
EOF
  for rep in $(ls -r | grep 'PA-*'); do
    echo "<li>"

    d=$(echo $rep \
        | sed 's|^...\([0-9][0-9]\)\([0-9][0-9]\)\([0-9][0-9]\).*$|20\1-\2-\3|')
    t=$(echo $rep \
        | sed 's|^..........\([0-9][0-9]\)\([0-9][0-9]\)\([0-9][0-9]\).*$|\1:\2:\3|')
    h=$(echo $rep \
        | awk -W lint=fatal -F "-" \
            '{print $4; \
              for(i=5; i<NF-1; i++) { \
                printf("-%s", $i)}}')
    b=$(echo $rep \
        | awk -W lint=fatal -F "-" '{print $NF}')
    printf "<a class='pa-link' href='%s'>%s \
              &nbsp;at&nbsp; %s \
              &nbsp;on&nbsp; %s \
              &nbsp;in&nbsp; %s</a>\n" \
           "$rep" "$d" "$t" "$h" "$b"

    echo "<br> &nbsp;"
    echo "<span class='it'>max ltac:</span> &nbsp;"
    cat "${rep}/proof-times.csv" \
      | awk -W lint=fatal -v key=2 -f "${PADIR}/csv-sort.awk" \
      | awk -W lint=fatal -F "," 'NR == 2 {print $1 " (" $2 " ms)"}'

    echo "<br> &nbsp;"
    echo "<span class='it'>max qed:</span> &nbsp;"
    cat "${rep}/proof-times.csv" \
      | awk -W lint=fatal -v key=3 -f "${PADIR}/csv-sort.awk" \
      | awk -W lint=fatal -F "," 'NR == 2 {print $1 " (" $2 " ms)"}'

    echo "<br> &nbsp;"
    echo "<span class='it'>build time:</span> &nbsp;"
    awk -W lint=fatal \
        'BEGIN { FS = ","; tot = 0 }  \
         { tot += $2 }      \
         END { print tot " s"}' \
        "${rep}/build-times.csv"

    if [ -f "${rep}/admit-count.txt" ]; then
      echo "<br> &nbsp;"
      echo "<span class='it'>admits:</span> &nbsp;"
      cat "${rep}/admit-count.txt"
    fi

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
