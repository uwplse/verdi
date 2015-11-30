#!/bin/sh
./scripts/stop-vard.sh
tmux new-session -d -s 'vard'
#tmux split-window -h 'OCAMLPROF_DUMP=/tmp/vard1.dump ./vard.p.native 1'
#tmux split-window -v -p 66 'OCAMLPROF_DUMP=/tmp/vard2.dump ./vard.p.native 2'
#tmux split-window -v -p 50 'OCAMLPROF_DUMP=/tmp/vard3.dump ./vard.p.native 3'
tmux split-window -h 'OCAMLVIZ_PORT=51000 ./vard.native 1'
tmux split-window -v -p 66 'OCAMLVIZ_PORT=51001 ./vard.native 2'
tmux split-window -v -p 50 'OCAMLVIZ_PORT=51002 ./vard.native 3'
tmux select-pane -L
exec tmux attach
