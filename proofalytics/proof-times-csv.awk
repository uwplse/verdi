BEGIN {
  FS = "__PROOFALYTICS__"
  tinit = -1
  name = ""
  t0 = tinit
  t1 = tinit
  t2 = tinit

  print "proof,ltac,qed,file,lineno"
}

{
  if(name != $3) {
    name = $3
    t0 = $1
    t1 = tinit
    t2 = tinit
  } else if(t1 == tinit) {
    t1 = $1
  } else if(t2 == tinit) {
    t2 = $1

    sub(/:$/, "", name)
    lt = (t1 - t0) / 1.0e6
    qt = (t2 - t1) / 1.0e6
    printf("%s,%.2f,%.2f,%s,%d\n", name, lt, qt, $2, $4)

    # some neighboring proofs have same name
    name = ""
  } else {
    print "proof-times-csv.awk: ERROR!" > "/dev/stderr"
    print "bad state in " FILENAME " line " FNR > "/dev/stderr"
    exit 1
  }
}
