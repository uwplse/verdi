#!/bin/sh
tmux new-session -d -s 'vard-debug'
tmux split-window -h './vard.native 1 -debug'
tmux split-window -v -p 66 './vard.native 2 -debug'
tmux split-window -v -p 50 './vard.native 3 -debug'
tmux select-pane -L
exec tmux attach
