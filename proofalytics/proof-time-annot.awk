/Lemma|Theorem|Corollary|Remark|Definition/ {
  fn = FILENAME
  sub(/^../, "", fn)
  tok = fn "__PROOFALYTICS__" $2 "__PROOFALYTICS__" FNR
}

/Qed\.|Defined\./ {
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}

{
  print $0
}

/^Proof\.|\sProof\./ {
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}

/Qed\.|Defined\./ {
  printf("Eval compute in ltac:(idtac \"%s\").\n", tok)
}
