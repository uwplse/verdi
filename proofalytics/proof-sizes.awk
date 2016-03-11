#!/usr/bin/env awk -f

/Lemma|Theorem|Definition/ {
  name  = $2
  start = FNR
  proof = ""
  lines = 0
  words = 0
}

{
  proof = proof $0
  lines = lines + 1
  words = words + NF
}

/Qed\./ {
  if(name != "") {
    sub(/:$/, "", name)
    printf("%s,%d,%d,%s,%d\n", name, lines, words, FILENAME, start)
  }
  name = ""
}
