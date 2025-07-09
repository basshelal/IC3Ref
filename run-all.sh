#!/usr/bin/env bash

scriptPath=$(realpath $0)
scriptDir=$(dirname "$scriptPath")
dir="$scriptDir/res/hwmcc08/*"

for filename in $dir;
do
  echo "$filename"
  ./run.sh "$filename" &
  if [[ $? != 0 && $? != 1 ]]; then
      echo " Failed at $filename"
      exit 69
  fi
done
