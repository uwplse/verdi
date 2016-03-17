BEGIN {
  FS = "-|:"
  if(commit == "") {
    commit = "master"
  }
  gh = "https://github.com/uwplse/verdi/blob/" commit
}

{
  if(NF == 0) {
    print ""
  } else {
    printf(" <a href='%s/%s#L%s'>%s:%s</a> ", gh, $1, $2, $1, $2)
    ln = $0
    sub(/^[^-:]*[-:][^-:]*[-:]/, "", ln)
    print ln
  }
}
