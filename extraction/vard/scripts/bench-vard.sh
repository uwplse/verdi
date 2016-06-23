#!/bin/bash

function start-vard {
  PORT=800${1}
  ./vard.native -dbpath "/tmp/vard-$PORT" \
                -port "$PORT" \
                -node 1,localhost:9001 -node 2,localhost:9002 -node 3,localhost:9003 \
                -me "$1" \
                > "/tmp/vard-${PORT}.log" &
  sleep 1
}

start-vard 1
start-vard 2
start-vard 3

python2 bench/setup.py --service vard --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003"
python2 bench/bench.py --service vard --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003" --threads 8 --requests 100

killall -9 vard.native > /dev/null
