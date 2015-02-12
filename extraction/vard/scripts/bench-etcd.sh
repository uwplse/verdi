#!/bin/sh

etcd --name=one \
     --listen-client-urls http://localhost:8001 \
     --advertise-client-urls http://localhost:8001 \
     --initial-advertise-peer-urls http://localhost:9001 \
     --listen-peer-urls http://localhost:9001 \
     --data-dir=/tmp/etcd1 \
     --initial-cluster "one=http://localhost:9001,two=http://localhost:9002,three=http://localhost:9003" \
      > /dev/null 2>&1 &
sleep 1

etcd --name=two \
     --listen-client-urls http://localhost:8002 \
     --advertise-client-urls http://localhost:8002 \
     --initial-advertise-peer-urls http://localhost:9002 \
     --listen-peer-urls http://localhost:9002 \
     --data-dir=/tmp/etcd2 \
     --initial-cluster "one=http://localhost:9001,two=http://localhost:9002,three=http://localhost:9003" \
      > /dev/null 2>&1 &
sleep 1

etcd --name=three \
     --listen-client-urls http://localhost:8003 \
     --advertise-client-urls http://localhost:8003 \
     --initial-advertise-peer-urls http://localhost:9003 \
     --listen-peer-urls http://localhost:9003 \
     --data-dir=/tmp/etcd3 \
     --initial-cluster "one=http://localhost:9001,two=http://localhost:9002,three=http://localhost:9003" \
     > /dev/null 2>&1 &
sleep 2

python2 bench/setup.py --service etcd --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003"
python2 bench/bench.py --service etcd --keys 50 --cluster "localhost:8001,localhost:8002,localhost:8003" --threads 8 --requests 100

killall -9 etcd
