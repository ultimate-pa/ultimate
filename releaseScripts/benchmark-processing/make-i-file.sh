#!/bin/bash
if [ ! -f "${1}" ];
  echo "Cannot find ${i}"
  exit 1
fi
gcc -E -P -m64 "${1}"
