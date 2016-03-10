#!/usr/bin/env awk -f

/Lemma|Theorem/ {
  name  = $2
  proof = ""
  lines = 0
  words = 0
}

{
  proof = proof $0
  lines = lines + 1
  words = words + NF
}

/Qed/ {
  sub(/:$/, "", name)
  printf("%s,%s,%d,%d,%d\n", FILENAME, name, lines, words, length(proof))
}
