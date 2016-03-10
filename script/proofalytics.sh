#!/usr/bin/env bash

set -e

BUILD_TIMES="build-times.csv"
PROOF_SIZES="proof-sizes.csv"

function main {
  build-times
  proof-sizes
}

function build-times {
  find . -name '*.buildtime' -exec cat {} \; \
    | sort --field-separator=, \
           --key=2 \
           --reverse \
           --numeric-sort \
    > "$BUILD_TIMES"
}

function proof-sizes {
  proofs-map measure-size > "$PROOF_SIZES"
}

function measure-size {
  vname="$(echo $1 | sed 's/^..//')"
  proof="$2"
  pname=$(grep 'Lemma\|Theorem' "$proof" | awk '{print $2}')
  sizes=$(wc "$proof" | awk '{printf("%d,%d,%d", $1, $2, $3)}')
  printf "%s,%s,%s\n" "$vname" "$pname" "$sizes"
}

function proofs-map {
  scratch="$(mktemp proofalytics-XXXXX)"
  for v in $(find . -name '*.v'); do
    inproof=false
    while read line; do
      if echo "$line" | grep --quiet 'Lemma\|Theorem'; then
        inproof=true
        echo > "$scratch"
      fi
      if $inproof; then
        echo "$line" >> "$scratch"
      fi
      if echo "$line" | grep --quiet 'Qed'; then
        inproof=false
        "$@" "$v" "$scratch"
      fi
    done < "$v"
  done
  rm -f "$scratch"
}

main
