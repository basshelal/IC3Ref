#!/usr/bin/env bash

make --jobs "$(nproc)" --keep-going --quiet && ./aiger/aigtoaig -a "$1" | ./IC3 -s -v
