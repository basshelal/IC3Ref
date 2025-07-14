#!/usr/bin/env bash

# Build entire project

scriptDir=$(dirname "$(realpath $0)")

# Build aiger
echo "Building aiger library" && \
cd "$scriptDir/aiger/" && \
./configure.sh -g && \
make

# Build minisat
echo "Building minisat library" && \
cd "$scriptDir/minisat/" && \
make

# Build ic3
echo "Building ic3"
cd "$scriptDir" && \
make
