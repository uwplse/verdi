#!/usr/bin/env bash

find . -name '*.buildtime' -exec cat {} \; \
  | sort --field-separator=, \
         --key=2 \
         --reverse \
         --numeric-sort \
  > build-times.csv

