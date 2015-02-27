#!/usr/bin/env bash
make -k -j 4
cd raft
make -k -j 4
cd proof
make -k -j 4
