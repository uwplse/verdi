set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents http://opam.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose
opam pin add coq-mathcomp-ssreflect $SSREFLECT_VERSION --yes --verbose
opam install StructTact InfSeqExt --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi-raft)
  opam install verdi-runtime --yes --verbose
  pushd ..
    git clone -b $VERDI_RAFT_BRANCH 'http://github.com/uwplse/verdi-raft'
    pushd verdi-raft
      Verdi_PATH=../verdi ./build.sh
    popd
  popd
  ;;
esac
