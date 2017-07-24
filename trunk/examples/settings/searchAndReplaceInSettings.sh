#!/bin/sh
# Script for replacing strings in all our settings files.
# You might want so use this after you updated preferences.
# This script might have some problems with special characters.
# Author: Matthias Heizmann
# Date: 2015-02-11


#quote oldstring
OLDSTRING=$(sed 's/\\/\\\\/g' <<< "$1")
NEWSTRING=$(sed 's/\\/\\\\/g' <<< "$2")
echo "Replacing the OLDSTRING with NEWSTRING in each .epf file"
echo "OLDSTRING: $1"
echo "NEWSTRING: $2"
#use comma as delimiter for sed because is hopefully does not occur in string
find . -name "*.epf" -exec sed -i -e "s,${OLDSTRING},${NEWSTRING}," {} \;
find ../../source/WebUltimateBridge/src/de/uni_freiburg/informatik/ultimate/webbridge/resources/settings/ -name "*.epf" -exec sed -i -e "s,${OLDSTRING},${NEWSTRING}," {} \;
