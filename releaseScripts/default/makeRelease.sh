#!/bin/bash
 
exitOnFail() {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with exit code $status"
		exit $status
    fi
    return $status
}

exitOnFailPop() {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with exit code $status"
		git stash pop
		exit $status
    fi
    return $status
}

abort() {
    read -r -p "${1:-Are you sure? [y/N]} " response
    case "$response" in
        [yY][eE][sS]|[yY]) 
            false
            ;;
        *)
            true
            ;;
    esac
}


DEPLOY_SERVER=sotec.informatik.uni-freiburg.de
DEPLOY_DIR=/export/server/httpd/ultimate/downloads/svcomp2017
TESTFILE=caniwrite
FILE="$DEPLOY_DIR"/"$TESTFILE"

exitOnFail git fetch --all --tags
exitOnFail git stash 
exitOnFailPop git rebase
exitOnFailPop git push 

CURRENTUSER=$(whoami)
HASH=`git rev-parse --short HEAD`
LAST_RELEASE=`git describe --tags $(git rev-list --tags --max-count=1)`
NEW_VERSION=`echo ${LAST_RELEASE:1} | awk -F. -v OFS=. 'NF==1{print ++$NF}; NF>1{if(length($NF+1)>length($NF))$(NF-1)++; $NF=sprintf("%0*d", length($NF), ($NF+1)%(10^length($NF))); print}'`
TO_GITHUB=false
TO_SOTEC=false
DEL_ZIP=true
POST_FINAL=false

while [[ $# -gt 1 ]]
do
	key="$1"
	case $key in
		-u|--user)
		CURRENTUSER="$2"
		shift # shift past the argument
		;;
		-v|--version)
		NEW_VERSION="$2"
		shift # shift past the argument
		;;
		--deploy-sotec)
		TO_SOTEC=true
		;;
		--post-final)
		POST_FINAL=true
		;;
		--deploy-github)
		TO_GITHUB=true
		RELEASE_REPO="-u ultimate-pa -r ultimate -s ""$2"
		shift # shift past the argument
		;;
		--keep-zip)
		DEL_ZIP=false
		;;

		*)
		# ignore unknown option
		;;
	esac
	shift # shift past argument or value
done

if abort "Making new release of version ${NEW_VERSION} for user ${CURRENTUSER}, continue [y/N]?" 
then
	echo "Aborted!"
	git stash pop 
	exit 1
fi

if [ "$TO_SOTEC" = true ] ;then
	echo "Enter password for user ${CURRENTUSER} on ${DEPLOY_SERVER}:" 
	read -s -p "Password: " SSHPASS
	echo 
	export SSHPASS
	sshpass -e ssh -oHostKeyAlgorithms=+ssh-dss $CURRENTUSER@$DEPLOY_SERVER "( test -e ${FILE} || touch ${FILE} ) && test -w ${FILE} && /usr/bin/rm ${FILE}"
	if [ ! $? -eq 0 ]; then 
		echo "Something is wrong with your write permissions to ${DEPLOY_DIR}, fix it before continuing"
		git stash pop
		exit 1
	fi
fi


pushd ../../trunk/source/BA_MavenParentUltimate/ > /dev/null
exitOnFailPop mvn org.eclipse.tycho:tycho-versions-plugin:set-version -DnewVersion="${NEW_VERSION}" -Dproperties="ultimate-version"
popd > /dev/null

# TODO: Run pre-deployment tests 

NEW_TAG="v${NEW_VERSION}"

exitOnFailPop git commit -a -m "update versions to ${NEW_VERSION} for new release"
exitOnFailPop git tag "${NEW_TAG}"
exitOnFailPop git fetch
exitOnFailPop git rebase
exitOnFailPop git push
exitOnFailPop git push origin --tags

pushd ../../trunk/source/BA_MavenParentUltimate/ > /dev/null
exitOnFailPop mvn clean install -Pmaterialize
popd > /dev/null


# createZip <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltl>
./createZip.sh Taipan linux AutomizerCInline_WitnessPrinter.xml NONE AutomizerCInline.xml AutomizerCInline_WitnessPrinter.xml NONE
./createZip.sh Automizer linux AutomizerC_WitnessPrinter.xml BuchiAutomizerCInline.xml AutomizerC.xml AutomizerC_WitnessPrinter.xml LTLAutomizerC.xml
./createZip.sh Kojak linux KojakC_WitnessPrinter.xml NONE NONE KojakC_WitnessPrinter.xml NONE

if [ "$TO_GITHUB" = true ]; then
	DESC=`git shortlog ${LAST_RELEASE}.. --no-merges --numbered -w0,6,9 --format="%s ( https://github.com/ultimate-pa/ultimate/commit/%h )"`
	echo "Creating release ${NEW_TAG}"
	github-release release ${RELEASE_REPO} -t "${NEW_TAG}" -d "${DESC}" --draft --pre-release

	for z in *.zip
	do 
		echo "Uploading file $z"
		github-release upload ${RELEASE_REPO} -t "${NEW_TAG}" --name "$z" --file "$z"
	done
fi

if [ "$TO_SOTEC" = true ] ;then
	if [ "$POST_FINAL" = true ]; then
		echo "Adding suffix to .zip files"
		for z in *.zip; do mv "$z" "${z%.zip}-post-final.zip"; done
	fi
	echo "Deploying to ${DEPLOY_SERVER}:${DEPLOY_DIR}"
	rsync -P --rsh="sshpass -e ssh -l me8 -oHostKeyAlgorithms=+ssh-dss" *.zip $CURRENTUSER@${DEPLOY_SERVER}:${DEPLOY_DIR}/. 
fi

if [ "$DEL_ZIP" = true ]; then 
	echo "Removing .zip files"
	rm *.zip 
fi

git stash pop 
exit 0

