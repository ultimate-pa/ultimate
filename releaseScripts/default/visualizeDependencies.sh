#!/bin/bash

for myfile in $(find $1 | grep MF$); do
  source=$(echo $myfile | awk -F/ '{ print $(NF-2) }')
  #echo "Looking at "$myfile" with content "`cat $myfile | tr '\n' ' ' | grep -o "Require-Bundle:[[:print:]]*"`
  for dep in $(cat $myfile | tr '\n' ' ' | grep -o "Require-Bundle:[[:print:]]*Bundle-RequiredExecutionEnvironment" | grep -iEo '[a-z]+[0-9]*[a-z]+.[a-z.|0-9]*' | grep '\.' | tr '\n' ' '); do
    echo "$source,$dep"
  done
done
