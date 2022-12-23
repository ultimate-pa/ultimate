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
usage() {
cat<<EOF
Usage: $0 [options]
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
      Only meaningful together with --deploy-server.
  -v, --version
      Specify new Ultimate version instead of just incrementing the z in the
      x.y.z versioning scheme.
  --deploy-github <token>
      Create a new release on Ultimate's Github repository; specify the API
      token that should be used to contact Github. 
  --deploy-server
      Copy all .zip files over to server specified in the settings.
  --keep-zip
      Do not cleanup .zip files.
  --post-final
      Add the suffix "-post-final" to the name of all .zip files before copying
      them to the remote server. No effect for Github release.
  --commit <hash>
      Use the specified commit hash instead of HEAD.
  --update-version
      Actually update the version
EOF
}

exit_with_clean_git_stack_on_fail() {
  "$@"
  local status=$?
  if [ $status -ne 0 ]; then
    echo "$* failed with exit code $status"
    git stash pop
    exit $status
  fi
  return $status
}

read_params() {
  # Local settings 
  DEPLOY_SERVER=sotec.informatik.uni-freiburg.de
  DEPLOY_DIR=/export/server/httpd/ultimate/downloads/svcomp2017
  TESTFILE=caniwrite
  FILE="$DEPLOY_DIR"/"$TESTFILE"
  HASH="$(git rev-parse HEAD)"

  # Get user params 
  while [[ $# -ge 1 ]]; do
    key="$1"
    case $key in
      -u|--user)
      CURRENTUSER="$2"
      shift
      ;;
      -v|--version)
      NEW_VERSION="$2"
      shift
      ;;
      --deploy-server)
      TO_SERVER=true
      test_if_cmd_is_available sshpass
      ;;
      --post-final)
      POST_FINAL=true
      ;;
      --deploy-github)
      TO_GITHUB=true
      GITHUB_TOKEN_CLASSIC="$2"
      # check if required tools are there 
      test_if_cmd_is_available github-release
      shift # shift past the argument
      ;;
      --keep-zip)
      DEL_ZIP=false
      ;;
      --commit)
      HASH="$(git rev-parse "$2")"
      shift
      ;;
      --update-version)
      UPDATE_VERSION=true
      ;;
      *)
      # quit if unknown option is there 
      usage
      exit 1
      ;;
    esac
    shift # shift past argument or value
  done
}

check_params() {
  # Ensure that we have a clean working directory 
  exit_on_fail git fetch --all --tags
  DEV_HEAD=$(git rev-parse origin/dev)

  if ! git cat-file -e "${HASH}^{commit}" ; then
    echo "$HASH is not a valid commit hash"
    exit 1
  fi
  if [ -z "$(git branch -r --contains "${HASH}")" ] ; then
    echo "$HASH is not on remote"
    exit 1
  fi
  

  if [ "$TO_SERVER" = true ] ; then
    echo "Enter password for user ${CURRENTUSER} on ${DEPLOY_SERVER}:" 
    read -r -s -p "Password: " SSHPASS
    echo 
    export SSHPASS
    sshpass -e ssh -oHostKeyAlgorithms=+ssh-dss "${CURRENTUSER}@$DEPLOY_SERVER" "( exit_on_fail -e ${FILE} || touch ${FILE} ) && exit_on_fail -w ${FILE} && /usr/bin/rm ${FILE}"
    if [ ! $? -eq 0 ]; then 
      echo "Something is wrong with your write permissions to ${DEPLOY_DIR}, fix it before continuing"
      git stash pop
      exit 1
    fi
  fi
}

prepare_environment() {
  exit_on_fail git stash
  exit_with_clean_git_stack_on_fail git rebase

  # Set variables not settable by user (and needed by defaults) 
  LAST_RELEASE=$(git tag -l --sort=-creatordate "v[0-9]*.[0-9]*.[0-9]*" | head -1)

  # Set defaults if variables are not set by user 
  : "${CURRENTUSER:=$(whoami)}"
  : "${NEW_VERSION:=$(echo "${LAST_RELEASE:1}" | awk -F. -v OFS=. 'NF==1{print ++$NF}; NF>1{if(length($NF+1)>length($NF))$(NF-1)++; $NF=sprintf("%0*d", length($NF), ($NF+1)%(10^length($NF))); print}')}"
  : "${TO_GITHUB:=false}"
  : "${TO_SERVER:=false}"
  : "${DEL_ZIP:=true}"
  : "${POST_FINAL:=false}"
}

create_and_tag_new_version() {
  # should we go? 
  if ! [ "$DEV_HEAD" == "$HASH" ] ; then
    if abort "Warning: 
dev is at $DEV_HEAD, but you want to tag $HASH as new release! 
This will 
* add a commit after that,
* modify all hashes since then, and
* require a force push to dev, which might lead to conflicts for other users.

Continue? [y/N]" ; then
      exit 1
    fi
  elif abort "Making new release of version ${NEW_VERSION} for user ${CURRENTUSER} and commit ${HASH}, continue [y/N]?" ; then
    echo "Aborted!"
    git stash pop 
    exit 1
  fi
  TMP_BRANCH="tmp/local_state"
  exit_on_fail git branch "$TMP_BRANCH"
  exit_on_fail git reset --hard "$HASH"
  spushd ../../trunk/source/BA_MavenParentUltimate/
  exit_with_clean_git_stack_on_fail mvn org.eclipse.tycho:tycho-versions-plugin:set-version -DnewVersion="${NEW_VERSION}" -Dproperties="ultimate-version"
  spopd

  # TODO: Run pre-deployment tests 

  NEW_TAG="v${NEW_VERSION}"
  exit_with_clean_git_stack_on_fail git commit -a -m "update versions to ${NEW_VERSION} for new release"
  exit_with_clean_git_stack_on_fail git tag -a "${NEW_TAG}" -m"Release new version ${NEW_VERSION}"
  exit_with_clean_git_stack_on_fail git rebase dev "$TMP_BRANCH"
  exit_with_clean_git_stack_on_fail git checkout dev
  exit_with_clean_git_stack_on_fail git merge --ff-only "$TMP_BRANCH"
  exit_with_clean_git_stack_on_fail git branch -d "$TMP_BRANCH"
}

deploy_new_version() {
  # actually build Ultimate
  RELEASE_TAGS=$(git tag -l --sort=-creatordate "v[0-9]*.[0-9]*.[0-9]*")
  CURRENT_VERSION=$(echo "$RELEASE_TAGS" | head -1)
  PREVIOUS_VERSION=$(echo "$RELEASE_TAGS" | head -2 | tail -1)
  
  if git rev-parse --verify -q release ; then
    echo "branch 'release' already exists, delete it before trying to deploy a new version"
    exit 1
  fi
  exit_on_fail git checkout "$CURRENT_VERSION" -b release
  exit_on_fail bash makeFresh.sh

  if [ "$TO_GITHUB" = true ]; then
    DESC=$(git shortlog "${PREVIOUS_VERSION}..${CURRENT_VERSION}" --no-merges --numbered -w0,6,9 --format="%s ( https://github.com/ultimate-pa/ultimate/commit/%h )")
    if [ ${#DESC} -ge $(getconf ARG_MAX) ] ; then
      echo "Description is too long, just using version"
      DESC="$CURRENT_VERSION"
    fi
    echo "Creating release ${CURRENT_VERSION}"
    github-release release -u ultimate-pa -r ultimate -s "${GITHUB_TOKEN_CLASSIC}" -t "${CURRENT_VERSION}" -d "${DESC}" --draft --pre-release

    for z in *.zip ; do 
      echo "Uploading file $z"
      github-release upload -u ultimate-pa -r ultimate -s "${GITHUB_TOKEN_CLASSIC}" -t "${CURRENT_VERSION}" --name "$z" --file "$z"
    done
  fi

  if [ "$TO_SERVER" = true ] ;then
    if [ "$POST_FINAL" = true ]; then
      echo "Adding suffix to .zip files"
      for z in *.zip; do mv "$z" "${z%.zip}-post-final.zip"; done
    fi
    echo "Deploying to ${DEPLOY_SERVER}:${DEPLOY_DIR}"
    rsync -P --rsh="sshpass -e ssh -l me8 -oHostKeyAlgorithms=+ssh-dss" ./*.zip $CURRENTUSER@${DEPLOY_SERVER}:${DEPLOY_DIR}/. 
    if [ "$POST_FINAL" = true ]; then
      echo "Adding suffix to .zip files"
      for z in *.zip; do mv "$z" "${z%.zip}-post-final.zip"; done
    fi
    echo "Deploying to ${DEPLOY_SERVER}:${DEPLOY_DIR}"
    rsync -P --rsh="sshpass -e ssh -l me8 -oHostKeyAlgorithms=+ssh-dss" ./*.zip $CURRENTUSER@${DEPLOY_SERVER}:${DEPLOY_DIR}/. 
  fi

  if [ "$DEL_ZIP" = true ]; then 
    echo "Removing .zip files"
    rm ./*.zip 
    echo "Removing .zip files"
    rm ./*.zip 
  fi
  
  exit_on_fail git checkout dev
  exit_on_fail git branch -D release
}

read_params "$@"
check_params
prepare_environment
if [ "$UPDATE_VERSION" = true ] ; then
  create_and_tag_new_version
  exit_with_clean_git_stack_on_fail git push --force-with-lease origin
  exit_with_clean_git_stack_on_fail git push --tags --force-with-lease origin
fi


if [ "$TO_GITHUB" = true ] || [ "$TO_SERVER" = true ] ; then
  deploy_new_version
fi

git stash pop 
exit 0