#!/bin/bash
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

DATE=$(date +%Y%m%d)
RUSER="jenkins-deploy"
RHOST="struebli.informatik.uni-freiburg.de"

deploy(){
  spushd "$(get_git_root)/releaseScripts/default"
  new_dir="${DATE}-${ULT_VERSION}"
  echo "Deploying Ultimate ${ULT_VERSION} by moving *.zip via SFTP to ${RHOST}:upload/${new_dir}"
  sftp -o StrictHostKeyChecking=no "${RUSER}@${RHOST}":upload/ <<< "mkdir ${new_dir}"
  for i in *.zip ; do
    sftp -o StrictHostKeyChecking=no "${RUSER}@${RHOST}":"upload/${new_dir}" <<< "put ${i}"
  done
  spopd
}

get_ult_version
deploy
