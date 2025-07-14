#!/usr/bin/env bash

# ./run.sh <FILE> where <FILE> is a path to an aiger file in .aag or .aig format

make --jobs "$(nproc)" --keep-going --quiet && ./aiger/aigtoaig -a "$1" | ./ic3 -s -v
