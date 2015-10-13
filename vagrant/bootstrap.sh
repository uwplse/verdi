#!/usr/bin/env bash

# Installs and configures VM for building and running Verdi

set -e
# useful packages
apt-get update
apt-get install -y git htop tmux

# setup verdi folder
if ! [ -L /home/vagrant/verdi ]; then
    rm -rf /home/vagrant/verdi
    ln -fs /vagrant /home/vagrant/verdi
fi

# install Coq 8.5beta2
apt-get install -y ocaml ocaml-native-compilers camlp4-extra
(
cd /home/vagrant
wget https://coq.inria.fr/distrib/V8.5beta2/files/coq-8.5beta2.tar.gz
tar xvf coq-8.5beta2.tar.gz
rm coq-8.5beta2.tar.gz
cd coq-8.5beta2
./configure -prefix /usr/local
make -j 2
make install
)

cat >> /home/vagrant/.bashrc <<- EOM
PS1='\[\e[0;32m\]\u\[\e[m\] \[\e[1;34m\]\w\[\e[m\] \[\e[1;32m\]\$\[\e[m\] \[\e[1;37m\]'
EOM

echo "Machine is now configured with base packages to compile and run Verdi"
echo "See ~/verdi/vagrant for additionally configuration scripts"
