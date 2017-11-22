#!/bin/bash

function exitOnFail {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with $1"
		exit $status
    fi
    return $status
}


DEPLOY_SERVER=sotec.informatik.uni-freiburg.de
DEPLOY_DIR=/export/server/httpd/ultimate/downloads/svcomp2018
TESTFILE=caniwrite
FILE="$DEPLOY_DIR"/"$TESTFILE"
SVCOMP_GITLAB_DIR=/storage/svcomp-archives/2018


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

exitOnFail bash makeFresh.sh

# uncomment this after the final release 
#for z in *.zip; do mv "$z" "${z%.zip}-post-final.zip"; done

# copy/rename to svcomp gitlab folder 
for z in *.zip; do
        f=$(echo $z | sed 's/Ultimate\(.*\)-linux\.zip/u\1\.zip/g' | tr '[:upper:]' '[:lower:]')
        cp "$z" "$SVCOMP_GITLAB_DIR""/""$f"
done

rsync -P --rsh="sshpass -e ssh -l me8 -oHostKeyAlgorithms=+ssh-dss" *.zip $CURRENTUSER@${DEPLOY_SERVER}:${DEPLOY_DIR}/. 
rm *.zip 

