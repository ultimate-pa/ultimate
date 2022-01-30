#!/bin/bash

if [ -z "$1" ]
then
	CURRENTUSER=$(whoami)
else
	CURRENTUSER="$1"
fi

#svn up ../../.
pushd ../../trunk/source/BA_MavenParentUltimate/
mvn clean install -Pmaterialize
popd

svn info ../../. > revision
./addRevision.sh Ultimate.py
./addRevision.sh UltimateWitnessChecker.py

./createZipAutomizer.sh
#./createZipCodeCheck.sh
scp *.zip revision $CURRENTUSER@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/downloads/2015witness/.
rm *.zip 
rm revision

