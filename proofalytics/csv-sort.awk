BEGIN {
  if(key == "") {
     key = 1
  }
  sort = "sort --field-separator=, --numeric-sort --reverse --key=" key
}

NR < 2 {
  print $0
  next
}

{
  print $0 | sort
}

END {
  close(sort)
}
