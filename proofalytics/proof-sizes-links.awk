#!/usr/bin/env awk -f

BEGIN {
  FS = ","
  if(commit == "") {
    commit = "master"
  }
  gh = "https://github.com/uwplse/verdi/blob/" commit
}

{
  if (NR == 1) {
    print $0
  } else {
    printf("<a href='%s/%s#L%s'>%s</a>,", gh, $4, $5, $1)
    printf("%s,%s,%s,%s\n", $2, $3, $4, $5)
  }
}
