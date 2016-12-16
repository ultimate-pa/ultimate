#!/bin/bash

DEPLOY_SERVER=sotec.informatik.uni-freiburg.de
DEPLOY_DIR=/export/server/httpd/ultimate/downloads/svcomp2017
TESTFILE=caniwrite
FILE="$DEPLOY_DIR"/"$TESTFILE"

if [ -z "$1" ]
then
	CURRENTUSER=$(whoami)
else
	CURRENTUSER="$1"
fi

echo "Enter password for user ${CURRENTUSER} on ${DEPLOY_SERVER}:" 
read -s -p "Password: " SSHPASS
echo 
export SSHPASS
sshpass -e ssh -oHostKeyAlgorithms=+ssh-dss $CURRENTUSER@$DEPLOY_SERVER "( test -e ${FILE} || touch ${FILE} ) && test -w ${FILE} && /usr/bin/rm ${FILE}"
if [ ! $? -eq 0 ]; then 
	echo "Something is wrong with your write permissions to ${DEPLOY_DIR}, fix it before continuing"
	exit 1
fi

pushd ../../trunk/source/BA_MavenParentUltimate/ > /dev/null
mvn clean install -Pmaterialize
popd > /dev/null

# createZip <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc>
./createZip.sh Taipan linux AutomizerC_WitnessPrinter.xml NONE AutomizerC.xml AutomizerC_WitnessPrinter.xml
./createZip.sh Automizer linux AutomizerC_WitnessPrinter.xml BuchiAutomizerCInline.xml AutomizerC.xml AutomizerC_WitnessPrinter.xml
./createZip.sh Kojak linux KojakC_WitnessPrinter.xml NONE NONE KojakC_WitnessPrinter.xml

rsync -P --rsh="sshpass -e ssh -l me8 -oHostKeyAlgorithms=+ssh-dss" *.zip $CURRENTUSER@${DEPLOY_SERVER}:${DEPLOY_DIR}/. 
rm *.zip 

