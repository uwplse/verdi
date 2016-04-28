#!/bin/bash

function start-vard-command {
  PORT=800${1}
  echo -e "./vard.native" "-dbpath \"/tmp/vard-$PORT\"" \
                          "-port \"$PORT\"" \
                          "-node 1,localhost:9001" "-node 2,localhost:9002" "-node 3,localhost:9003" \
                          "-me \"$1\""
}

tmux new-session -d -s 'vard'
tmux split-window -h "$(start-vard-command 1)"
tmux split-window -v -p 66 "$(start-vard-command 2)"
tmux split-window -v -p 50 "$(start-vard-command 3)"
tmux select-pane -L
exec tmux attach
