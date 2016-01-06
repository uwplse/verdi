#!/bin/sh

OCAMLVIZ_PORT=5001 ./vard.native 1 > /dev/null 2>&1 &
sleep 1
OCAMLVIZ_PORT=5002 ./vard.native 2 > /dev/null 2>&1 &
sleep 1
OCAMLVIZ_PORT=5003 ./vard.native 3 > /dev/null 2>&1 &
sleep 1

python2 bench/setup.py --service vard --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003"
python2 bench/bench.py --service vard --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003" --threads 8 --requests 100

read -p 'Press <enter> to stop vard instances" IGNORE
killall -9 vard.native
