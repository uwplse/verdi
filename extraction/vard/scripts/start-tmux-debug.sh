#!/bin/sh
tmux new-session -d -s 'vard-debug'
tmux split-window -h
tmux send-keys './vard.native 1 -debug' C-m
tmux split-window -v -p 66
tmux send-keys './vard.native 2 -debug' C-m
tmux split-window -v -p 50
tmux send-keys './vard.native 3 -debug' C-m
tmux select-pane -L
exec tmux attach
