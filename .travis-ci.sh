#!/usr/bin/env bash

set -ev

export DOWNSTREAM=$1

eval $(opam config env)

opam update

opam pin add verdi . --yes --verbose

case $DOWNSTREAM in
verdi-raft)
  opam install verdi-raft --yes --verbose
  ;;
esac
