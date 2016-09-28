set -ev

pushd ..
  wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
  tar xf coq-8.5-build-local.tgz
  export PATH=$PWD/coq-8.5/bin:$PATH

  git clone 'http://github.com/uwplse/StructTact'
  pushd StructTact
    ./build.sh
  popd
popd

./build.sh

pushd ..
  git clone 'http://github.com/uwplse/verdi-raft'
  pushd verdi-raft
    ./build.sh
  popd
popd
