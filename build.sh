#!/usr/bin/env bash

# Build everything needed

scriptPath=$(realpath $0)
scriptDir=$(dirname "$scriptPath")

echo "Building aiger library" && \
cd "$scriptDir/aiger/" && \
./configure.sh -g && \
make

echo "Building minisat library" && \
cd ../minisat && \
make

echo "Building ic3"
cd ../ && \
make
