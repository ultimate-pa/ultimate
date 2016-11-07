#!/bin/bash

if [ -z "$1" ]
then
	CURRENTUSER=$(whoami)
else
	CURRENTUSER="$1"
fi

pushd ../../trunk/source/BA_MavenParentUltimate/
mvn clean install -Pmaterialize
popd

./createZipAutomizer.sh linux
./createZipAutomizer.sh win32
#./createZipCodeCheck.sh

#scp -oHostKeyAlgorithms=+ssh-dss *.zip $CURRENTUSER@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/downloads/svcomp2016/.
#rm *.zip 
#rm revision

