#!/bin/bash

function start-vard-command {
  PORT=800${1}
  echo -e "./vard.native" "-dbpath \"/tmp/vard-$PORT\"" \
                          "-port \"$PORT\"" \
                          "-node 1,localhost:9001" "-node 2,localhost:9002" "-node 3,localhost:9003" \
                          "-me \"$1\"" \
                          "-debug"
}

tmux new-session -d -s 'vard-debug'
tmux split-window -h
tmux send-keys "$(start-vard-command 1)" C-m
tmux split-window -v -p 66
tmux send-keys "$(start-vard-command 2)" C-m
tmux split-window -v -p 50
tmux send-keys "$(start-vard-command 3)" C-m
tmux select-pane -L
exec tmux attach
