#!/bin/bash
# Install vard and etcd on a machine running the EC2 Ubuntu AMI

# install dependencies: git, make, ocaml, coq
echo "yes" | add-apt-repository ppa:avsm/ocaml41+opam12
apt-get update -qq
apt-get install -qq git make ocaml ocaml-native-compilers camlp4-extra
wget http://homes.cs.washington.edu/~jrw12/coq-8.5beta2-build.tgz
tar xf coq-8.5beta2-build.tgz
pushd coq-8.5beta2
make install > /dev/null 2>&1
popd

# vard
git clone https://github.com/uwplse/verdi.git
pushd verdi
make vard
popd
ln -s verdi/extraction/vard vard

# etcd
curl -L https://github.com/coreos/etcd/releases/download/v2.0.9/etcd-v2.0.9-linux-amd64.tar.gz -o etcd-v2.0.9-linux-amd64.tar.gz
tar xzf etcd-v2.0.9-linux-amd64.tar.gz
ln -s etcd-v2.0.9-linux-amd64 etcd
