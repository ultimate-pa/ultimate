#!/bin/bash

if [ -z "$1" ]
then
	CURRENTUSER=$(whoami)
else
	CURRENTUSER="$1"
fi

#svn up ../../.
#pushd ../../trunk/source/BA_MavenParentUltimate/
#mvn clean install -Pmaterialize
#popd

./createZipAutomizer.sh
./createZipCodeCheck.sh
svn info ../../. > revision
scp *.zip revision $CURRENTUSER@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/downloads/svcomp2015/.
rm *.zip 
rm revision

