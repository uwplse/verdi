#!/bin/sh

set -ev

export DOWNSTREAM=$1

opam update --yes

opam pin add verdi . --yes --verbose

case $DOWNSTREAM in
verdi-raft)
  opam install verdi-raft --yes --verbose
  ;;
esac
