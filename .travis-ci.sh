set -ev

opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect --yes --verbose

pushd ..
  git clone -b $STRUCTTACT_BRANCH 'http://github.com/uwplse/StructTact'
  pushd StructTact
    ./build.sh
  popd

  git clone 'http://github.com/palmskog/InfSeqExt'
  pushd InfSeqExt
    ./build.sh
  popd
popd

./build.sh

case $DOWNSTREAM in
verdi-raft)
  pushd ..
    git clone -b $VERDI_RAFT_BRANCH 'http://github.com/uwplse/verdi-raft'
    pushd verdi-raft
      ./build.sh
    popd
  popd
  ;;
esac
