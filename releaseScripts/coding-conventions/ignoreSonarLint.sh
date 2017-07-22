#!/bin/bash
#
# Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
#
# -----------------------------------------------------------------------------
#
# Creates a folder called '.settings' containing a file called
# 'org.sonarlint.eclipse.core.prefs' in all subfolders of the 'source' folder.
# The file will contain the following text:
#
# autoEnabled=false
# eclipse.preferences.version=1
# extraProperties=
#
# -----------------------------------------------------------------------------
#
# Instructions:
# Pass the path to Ultimate's 'source' folder to this script.
#
# Example:
# ./ignoreSonarLint /home/johndoe/ultimate/trunk/source/
#
# -----------------------------------------------------------------------------

PATH_TO_SOURCE=$1
SETTINGS="/.settings"
FILE="$SETTINGS/org.sonarlint.eclipse.core.prefs"

for FOLDER in $(find $PATH_TO_SOURCE -maxdepth 1 -mindepth 1 -type d); do
	# exclude folders starting with '.'
	SHORT_NAME=$(basename "$FOLDER")
	if [[ "${SHORT_NAME:0:1}" != "." ]] ;
	then
		if [[ -e "$FOLDER" ]] ;
		then
			echo "folder $FOLDER already exists"
		else
			echo "creating folder $FOLDER"
			mkdir "$FOLDER$SETTINGS"
		fi
		if [[ -e "$FOLDER$FILE" ]] ;
		then
			echo "file already exists, overwriting"
		else
			echo "creating file $FOLDER$FILE"
			touch "$FOLDER$FILE"
		fi
		echo -e "autoEnabled=false\neclipse.preferences.version=1\nextraProperties=" > "$FOLDER$FILE"
	else
		echo "ignoring folder $FOLDER"
	fi
done