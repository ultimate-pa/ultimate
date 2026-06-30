#!/bin/sh
# Script for replacing strings in all our settings files.
# You might want so use this after you updated preferences.
#
# Warning: This script might have some problems with special characters.
#
# Usage:
# Go to the trunk/examples/settings folder
# Call the following command. Don't forget the quote symbols.
# Use the whole settings string that usually starts with /instance.
# ./searchAndReplaceInSettings.sh [OLDSTRING] [NEWSTRING]
#
# The replacement will be done in all subfolders of trunk/examples/settings
#
# Check if your replacement was successful using
# grep -ir SOME_KEYWORD .
#
# Author: Matthias Heizmann, Claus Schaetzle
# Date: 2015-02-11


# Convert a raw string into a basic regular expression for a sed s/.../.../ command
sedQuote() {
    echo "$*" | sed 's/[][/\.*$^]/\\&/g'
}

echo "Replacing the OLDSTRING with NEWSTRING in each .epf file"
echo "OLDSTRING: $1"
echo "NEWSTRING: $2"
old="$(sedQuote "$1")"
new="$(sedQuote "$2")"
find .. -name \*.epf -exec sed -i -e "s/$old/$new/g" {} +

