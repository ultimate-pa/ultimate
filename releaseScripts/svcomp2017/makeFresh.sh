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

./createZip.sh Taipan linux AutomizerC_WitnessPrinter.xml
./createZip.sh Automizer linux AutomizerC_WitnessPrinter.xml BuchiAutomizerCWithBlockEncoding.xml AutomizerC.xml
./createZip.sh Kojak KojakC.xml linux 

#scp -oHostKeyAlgorithms=+ssh-dss *.zip $CURRENTUSER@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/downloads/svcomp2016/.
#rm *.zip 
#rm revision

