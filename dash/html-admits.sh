#!/usr/bin/env bash

ROOT=".."
COQ="$(find "$ROOT" -name '*.v')"

function main {
  cat <<HERE
<html>
<head>
  <title>Verdi admits</title>
  <link rel='stylesheet' type='text/css' href='admits.css'>
</head>
<body>
HERE

  echo "<h1>"
  grep --ignore-case admit $COQ \
    | wc -l
  echo " admits found in Verdi</h1>"
  echo "<pre>"
  grep --ignore-case --context=3 --line-number admit $COQ \
    | sed 's/admit/<span class="red">admit<\/span>/g' \
    | sed 's/Admitted/<span class="red">Admitted<\/span>/g'

  cat <<HERE
</pre>
</body>
</html>
HERE
}

main > admits.html
