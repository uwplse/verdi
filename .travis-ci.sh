echo "yes" | sudo add-apt-repository ppa:avsm/ocaml41+opam12
sudo apt-get update -qq
sudo apt-get install -qq ocaml ocaml-native-compilers camlp4-extra
wget http://homes.cs.washington.edu/~jrw12/coq-8.5beta1-build.tgz
tar xf coq-8.5beta1-build.tgz
pushd coq-8.5beta1
sudo make install > /dev/null 2>&1
popd
./build.sh
