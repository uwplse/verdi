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
    printf("<a href='%s/%s.v'>%s.v</a>,%s\n", gh, $1, $1, $2)
  }
}
