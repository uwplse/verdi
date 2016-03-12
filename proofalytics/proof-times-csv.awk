BEGIN {
  FS = "__PROOFALYTICS__"
  name = ""
  t0 = 0
  t1 = 0
  t2 = 0
}

{
  if(name != $3) {
    name = $3
    t0 = $1
  } else if(t1 == 0) {
    t1 = $1
  } else if(t2 == 0) {
    t2 = $1
    printf("%s,%f,%f,%s,%d\n", name, t1 - t0, t2 - t1, $2, $4)

    name = ""
    t0 = 0
    t1 = 0
    t2 = 0
  } else {
    print "proof-times-csv.awk: ERROR!" > "/dev/stderr"
    print "bad state on line " FNR > "/dev/stderr"
    exit 1
  }
}
