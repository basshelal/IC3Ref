#!/usr/bin/env bash

# Clean entire project

scriptDir=$(dirname "$(realpath $0)")

# Clean aiger
echo "Cleaning aiger" && \
cd "$scriptDir/aiger/" && \
make clean

# Clean minisat
echo "Cleaning minisat" && \
cd "$scriptDir/minisat/" && \
make clean

# Clean ic3
echo "Cleaning ic3"
cd "$scriptDir" && \
make clean
