#!/bin/sh

./vard.native 1 2>&1 > /dev/null &
sleep 1
./vard.native 2 2>&1 > /dev/null &
sleep 1
./vard.native 3 2>&1 > /dev/null &
sleep 1

python bench/setup.py --service vard --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003"
python bench/bench.py --service vard --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003" --threads 8 --requests 100

killall -13 vard.native 2>&1 > /dev/null
