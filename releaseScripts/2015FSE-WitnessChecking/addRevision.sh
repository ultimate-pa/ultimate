#!/bin/bash

REVISION=`svn info ../../. | grep '^Revision:' | sed -e 's/^Revision: //'`
awk -v rev=$REVISION '/svnRevNumber = '"'"'.*'"'"'/ { print "svnRevNumber = '"'"'" rev "'"'"'"; next }1' "$1" > "$1".tmp && mv "$1".tmp "$1"