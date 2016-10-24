set -ev

pushd ..
  wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
  tar xf coq-8.5-build-local.tgz
  export PATH=$PWD/coq-8.5/bin:$PATH

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
