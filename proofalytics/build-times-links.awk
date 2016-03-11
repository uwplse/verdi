#!/usr/bin/env awk -f

BEGIN {
  FS = ","
  gh = "https://github.com/uwplse/verdi/blob/master"
}

{
  if (NR == 1) {
    print $0
  } else {
    printf("<a href='%s/%s.v'>%s.v</a>,%s\n", gh, $1, $1, $2)
  }
}
