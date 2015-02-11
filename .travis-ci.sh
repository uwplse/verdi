echo "yes" | sudo add-apt-repository ppa:avsm/ocaml41+opam12
sudo apt-get update -qq
sudo apt-get install -qq ocaml ocaml-native-compilers camlp4-extra opam
export OPAMYES=1
opam init
eval `opam config env`
opam repo add coq-8.5 https://github.com/coq/repo-8.5.git
opam install coq
make
