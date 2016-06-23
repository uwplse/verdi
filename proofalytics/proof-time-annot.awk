/^[[:space:]]*(Lemma|Theorem|Corollary|Remark|Definition)/ {
  fn = FILENAME
  sub(/^../, "", fn)
  tok = fn "__PROOFALYTICS__" $2 "__PROOFALYTICS__" FNR
}

/^[[:space:]]*(Qed|Defined)\./ {
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}

{
  print $0
}

/^[[:space:]]*Proof\./ {
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}

/^[[:space:]]*(Qed|Defined)\./ {
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}
