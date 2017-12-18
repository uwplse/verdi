set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq ${COQ_VERSION} --yes --verbose
opam pin add coq-mathcomp-ssreflect ${SSREFLECT_VERSION} --yes --verbose

opam pin add verdi . --yes --verbose

case $DOWNSTREAM in
verdi-raft)
  opam install verdi-raft --yes --verbose
  ;;
esac
