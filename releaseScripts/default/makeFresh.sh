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

#svn info ../../. > revision
#REVISION=`svn info ../../. | grep '^Revision:' | sed -e 's/^Revision: //'`
#awk -v rev=$REVISION '/svnRevNumber = '"'"'.*'"'"'/ { print "svnRevNumber = '"'"'" rev "'"'"'"; next }1' Ultimate.py > Ultimate.py.tmp && mv Ultimate.py.tmp Ultimate.py

./createZipAutomizer.sh linux
./createZipAutomizer.sh win32
#./createZipCodeCheck.sh
#scp -oHostKeyAlgorithms=+ssh-dss *.zip $CURRENTUSER@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/downloads/svcomp2016/.
#rm *.zip 
#rm revision

