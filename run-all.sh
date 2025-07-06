#!/usr/bin/env bash

scriptDir=$(basename "$0")
dir="$scriptDir/res/hwmcc08/*"

for filename in $dir;
do
  echo "$filename"
  ./run.sh "$filename"
  if [[ $? != 0 && $? != 1 ]]; then
      echo " Failed at $filename"
      exit 69
  fi
done
