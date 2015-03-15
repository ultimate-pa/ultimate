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
REVISION=`svn info ../../. | grep '^Revision:' | sed -e 's/^Revision: //'`
awk -v rev=$REVISION '/svnRevNumber = '"'"'.*'"'"'/ { print "svnRevNumber = '"'"'" rev "'"'"'"; next }1' Ultimate.py > Ultimate.py.tmp && mv Ultimate.py.tmp Ultimate.py
awk -v rev=$REVISION '/svnRevNumber = '"'"'.*'"'"'/ { print "svnRevNumber = '"'"'" rev "'"'"'"; next }1' UltimateWitnessChecker.py > UltimateWitnessChecker.py.tmp && mv UltimateWitnessChecker.py.tmp UltimateWitnessChecker.py

./createZipAutomizer.sh
#./createZipCodeCheck.sh
scp *.zip revision $CURRENTUSER@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/downloads/2015witness/.
rm *.zip 
rm revision

