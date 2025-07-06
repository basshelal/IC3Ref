#!/usr/bin/env bash

make && ./aiger/aigtoaig -a "$1" | ./IC3 -v -d -s
