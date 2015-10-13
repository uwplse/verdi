#!/usr/bin/env bash

# Installs and configures NeoVim with coqtop support

set -e
# configure tmux
cat > /home/vagrant/.tmux.conf <<- EOM
setw -g mode-keys vi
bind k selectp -U # switch to panel Up
bind j selectp -D # switch to panel Down 
bind h selectp -L # switch to panel Left
bind l selectp -R # switch to panel Right
set -g prefix C-a
unbind-key C-b
bind-key C-a send-prefix
EOM

# install NeoVim
echo yes | add-apt-repository ppa:neovim-ppa/unstable
apt-get update
apt-get install -y neovim python-dev python-pip python-greenlet python-lxml
pip install neovim

# configure NeoVim
mkdir -p /home/vagrant/.nvim/autoload
mkdir -p /home/vagrant/.nvim/bundle
curl -LSso /home/vagrant/.nvim/autoload/pathogen.vim https://tpo.pe/pathogen.vim
(
cd /home/vagrant
git clone -b 8.5b2 https://github.com/epdtry/neovim-coq.git
cd .nvim/bundle
git clone https://github.com/tpope/vim-sensible.git
git clone https://github.com/jvoorhis/coq.vim.git
)
cat > /home/vagrant/.nvimrc <<- EOM
execute pathogen#infect()
nnoremap CL :call rpcstart("python", ["/home/vagrant/neovim-coq/test.py"])<CR>
EOM
