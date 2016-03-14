/Lemma|Theorem|Corollary|Remark|Definition/ {
  name  = $2
  start = FNR
  proof = ""
  lines = 0
  words = 0

  print "proof,lines,words,file,lineno"
}

{
  proof = proof $0
  lines = lines + 1
  words = words + NF
}

/Qed\.|Defined\./ {
  if(name != "") {
    sub(/:$/, "", name)
    printf("%s,%d,%d,%s,%d\n", name, lines, words, FILENAME, start)
  }
  name = ""
}
