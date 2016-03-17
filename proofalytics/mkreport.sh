#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOF_SIZES="${PADIR}/proof-sizes.csv"
BUILD_TIMES="${PADIR}/build-times.csv"
PROOF_TIMES="${PADIR}/proof-times.csv"

INDEX="${PADIR}/index.html"
COMMIT="$(git rev-parse HEAD)"


# save admit count for toplevel index
NADMIT=$(find "${PADIR}/.." -name '*.v' \
           | xargs grep --ignore-case 'admit' \
           | wc -l)
echo "$NADMIT" > "${PADIR}/admit-count.txt"

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
      font-size: 12pt;
    }
    #nav {
      padding: 0 0 10px 10px;
      margin: 0;
    }
    #nav li {
      display: inline;
      padding-right: 15px;
    }
    .it {
      font-style: italic;
    }
    .bf {
      font-weight: bold;
    }
    .red {
      color: red;
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
    pre {
      line-height: 150%;
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
  <ul id='nav'><li>
    <a href='#proof-times'>Proof Times</a>
  </li><li>
    <a href='#build-times'>Build Times</a>
  </li><li>
    <a href='#admits'>Admits</a>
  </li><li>
    <a href='#proof-sizes'>Proof Sizes</a>
  </li></ul>
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
  </tr><tr>
    <td class='cfg-fld'>Coqwc</td>
    <td>
      $(find "${PADIR}/.." -name '*.v' \
          | xargs coqwc \
          | awk 'END { printf("spec = %'"'"'d &nbsp; &nbsp; proof = %'"'"'d\n", $1, $2) }')
    </td>
  </tr><tr>
    <td class='cfg-fld'>Compile</td>
    <td>
      $([ -f "$BUILD_TIMES" ] &&  \
          awk 'BEGIN { FS = ","; tot = 0 }  \
               { tot += $2 }      \
               END { print tot " sec"}' \
              "$BUILD_TIMES")
    </td>
  </tr><tr>
    <td class='cfg-fld'>Admits</td>
    <td>$NADMIT</td>
  </tr></table>
EOF

  if [ -f "$PROOF_TIMES" ]; then
    echo "<a id='proof-times'></a>"
    echo "<h2>Proof Times</h2>"
    echo "<div class='scroller'>"
    cat "$PROOF_TIMES" \
      | awk -v commit="$COMMIT" \
            -f "${PADIR}/proof-times-links.awk" \
      | awk -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi

  if [ -f "$BUILD_TIMES" ]; then
    echo "<a id='build-times'></a>"
    echo "<h2>Build Times</h2>"
    echo "<div class='scroller'>"
    cat "$BUILD_TIMES" \
      | awk -v commit="$COMMIT" \
            -f "${PADIR}/build-times-links.awk" \
      | awk -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi

  echo "<a id='admits'></a>"
  echo "<h2>Admits</h2>"
  echo -n "<div class='scroller'><pre><code>"
  find "${PADIR}/.." -name '*.v' \
    | xargs grep --context=4 \
                 --line-number \
                 --ignore-case 'admit' \
    | sed -e "s|^${PADIR}/\.\./||" \
          -e 's|^--$||' \
          -e 's|admit|<span class="bf red">admit</span>|g' \
          -e 's|Admitted|<span class="bf red">Admitted</span>|g' \
    | awk -v commit="$COMMIT" \
          -f "${PADIR}/admits-links.awk"
  echo "</code></pre></div>"

  if [ -f "$PROOF_SIZES" ]; then
    echo "<a id='proof-sizes'></a>"
    echo "<h2>Proof Sizes</h2>"
    echo "<div class='scroller'>"
    cat "$PROOF_SIZES" \
      | awk -v commit="$COMMIT" \
            -f "${PADIR}/proof-sizes-links.awk" \
      | awk -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi

  cat <<EOF
</body>
</html>
EOF
}

mkindex > "$INDEX"
