wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
tar xf coq-8.5-build-local.tgz
export PATH=$PWD/coq-8.5/bin:$PATH

./build.sh
