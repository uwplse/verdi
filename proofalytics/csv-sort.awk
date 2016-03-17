BEGIN {
 if(key == "") {
    key = 1
  }
}

NR < 2 {
  print $0
  next
}

{
  print $0 | "sort --field-separator=, --numeric-sort --reverse --key=" key
}
