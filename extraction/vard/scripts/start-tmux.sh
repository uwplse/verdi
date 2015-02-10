#!/bin/sh
tmux new-session -d -s 'vard'
tmux split-window -h './vard.native 1'
tmux split-window -v -p 66 './vard.native 2'
tmux split-window -v -p 50 './vard.native 3'
tmux select-pane -L
exec tmux attach
