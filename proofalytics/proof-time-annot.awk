function reset() {
  file = ""
  name = ""
  line = ""
  prog = 0
  oblg = 0
}

function beep() {
  if(file == "") {
    print "proof-time-annot.awk: ERROR!" > "/dev/stderr"
    print "no token in " FILENAME " line " FNR > "/dev/stderr"
    close("/dev/stderr")
    exit 1
  }
  if(prog) {
    tok = file "__PROOFALYTICS__" name "@" oblg "__PROOFALYTICS__" line
  } else {
    tok = file "__PROOFALYTICS__" name "__PROOFALYTICS__" line
  }
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}

BEGIN {
  reset()
}

/^[[:space:]]*(Lemma|Theorem|Example|Corollary|Remark|Definition|Fixpoint|Instance)/ {
  reset()
  file = FILENAME
  sub(/^../, "", file)
  name = $2
  line = FNR
}

/^[[:space:]]*Program Definition/ {
  reset()
  file = FILENAME
  sub(/^../, "", file)
  name = $3
  line = FNR
  prog = 1
  oblg = 0
}

/^[[:space:]]*(Qed|Defined)\./ {
  beep()
}

{
  print $0
}

/^[[:space:]]*Proof\./ {
  beep()
}

/^[[:space:]]*Next Obligation\./ {
  oblg = oblg + 1
  beep()
}

/^[[:space:]]*(Qed|Defined)\./ {
  beep()
  if(!prog) {
    reset()
  }
}
