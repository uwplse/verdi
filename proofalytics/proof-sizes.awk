# TODO support Program Definition

function reset() {
  name  = ""
  start = 0
  proof = ""
  lines = 0
  words = 0
}

BEGIN {
  print "proof,lines,words,file,lineno"
  reset()
}

/Lemma|Theorem|Example|Corollary|Remark|Definition|Fixpoint|Instance/ {
  reset()
  name  = $2
  start = FNR
}

{
  proof = proof $0
  lines = lines + 1
  words = words + NF
}

/Qed\.|Defined\./ {
  if(name != "") {
    sub(/:$/, "", name)
    fn = FILENAME
    sub(/^.*\.\.\//, "", fn)
    printf("%s,%d,%d,%s,%d\n", name, lines, words, fn, start)
  }
  reset()
}
