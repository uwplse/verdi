wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
tar xf coq-8.5-build-local.tgz
export PATH="$PWD/coq-8.5/bin:$PATH"

wget 'http://homes.cs.washington.edu/~ztatlock/mathcomp.tgz'
tar xf mathcomp.tgz
export mathcomp_PATH="$PWD/mathcomp/mathcomp"

./build.sh
