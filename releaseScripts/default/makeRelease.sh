#!/bin/bash
# This script creates a new release of Ultimate tools on Github and possibly on a custom webserver. 
# It requires the github-release binary https://github.com/aktau/github-release 
# 

## Include the makeSettings shared functions 
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"


## Start the actual script
# Local functions 
function usage {
cat<<EOF
Usage: $0 options
This script creates a new release for the Ultimate tools. It
 - ensures that the current working directory is clean,
 - updates the version number of all Ultimate tools with Maven,
 - creates a new commit and tag, and
 - pushs them.
Optionally, it builds a release from the new Ultimate version by calling 
makeFresh.sh and pushes it to Github and/or some server via SSH.

OPTIONS:

  -u <name>, --user <name>
      User name that should be used if deploying to a remote server via SSH. 
      Only meaningful together with --deploy-server
  -v, --version
      Specify new Ultimate version instead of just incrementing the z in the
      versioning scheme x.y.z 
  --deploy-github <id>
      Create a new release on Ultimate's Github repository; specify the API
      token that should be used to contact Github. 
  --deploy-server
      Copy all .zip files over to server specified in the settings. 
  --keep-zip
      Do not cleanup .zip files
  --post-final
      Add the suffix "-post-final" to the name of all .zip files before copying
      them to the remote server. No effect for Github release.
EOF
}

testPopOnFail() {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with exit code $status"
		git stash pop
		exit $status
    fi
    return $status
}

# Local settings 
DEPLOY_SERVER=sotec.informatik.uni-freiburg.de
DEPLOY_DIR=/export/server/httpd/ultimate/downloads/svcomp2017
TESTFILE=caniwrite
FILE="$DEPLOY_DIR"/"$TESTFILE"

# Get user params 
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
        --deploy-server)
        TO_SERVER=true
        ;;
        --post-final)
        POST_FINAL=true
        ;;
        --deploy-github)
        TO_GITHUB=true
        RELEASE_REPO="-u ultimate-pa -r ultimate -s ""$2"
        # check if required tools are there 
        test_if_cmd_is_available github-release
        shift # shift past the argument
        ;;
        --keep-zip)
        DEL_ZIP=false
        ;;
    
        *)
        # quit if unknown option is there 
        usage
        exit 1
        ;;
    esac
    shift # shift past argument or value
done

# Ensure that we have a clean working directory 
test git fetch --all --tags
test git stash 
testPopOnFail git rebase
testPopOnFail git push 

# Set variables not settable by user (and needed by defaults) 
HASH=`git rev-parse --short HEAD`
LAST_RELEASE=`git describe --tags $(git rev-list --tags --max-count=1)`

# Set defaults if variables are not set by user 
: ${CURRENTUSER:=$(whoami)}
: ${NEW_VERSION:=`echo ${LAST_RELEASE:1} | awk -F. -v OFS=. 'NF==1{print ++$NF}; NF>1{if(length($NF+1)>length($NF))$(NF-1)++; $NF=sprintf("%0*d", length($NF), ($NF+1)%(10^length($NF))); print}'`}
: ${TO_GITHUB:=false}
: ${TO_SERVER:=false}
: ${DEL_ZIP:=true}
: ${POST_FINAL:=false}

# should we go? 
if abort "Making new release of version ${NEW_VERSION} for user ${CURRENTUSER}, continue [y/N]?" 
then
	echo "Aborted!"
	git stash pop 
	exit 1
fi

if [ "$TO_SERVER" = true ] ;then
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
testPopOnFail mvn org.eclipse.tycho:tycho-versions-plugin:set-version -DnewVersion="${NEW_VERSION}" -Dproperties="ultimate-version"
popd > /dev/null

# TODO: Run pre-deployment tests 

NEW_TAG="v${NEW_VERSION}"

testPopOnFail git commit -a -m "update versions to ${NEW_VERSION} for new release"
testPopOnFail git tag "${NEW_TAG}"
testPopOnFail git fetch
testPopOnFail git rebase
testPopOnFail git push
testPopOnFail git push origin --tags

# actually build Ultimate 
test bash makeFresh.sh

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

if [ "$TO_SERVER" = true ] ;then
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

