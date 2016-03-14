#!/usr/bin/env bash
./configure
make -k
cd proofalytics
make
make publish
