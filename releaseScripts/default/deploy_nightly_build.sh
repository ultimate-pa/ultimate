#!/bin/bash
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

DATE=$(date +%Y%m%d)
RUSER="ultimate-nightly"
RHOST="mariachi.informatik.uni-freiburg.de"
PORT=2222
TARGET_DIR="/fstorage/shared/ultimate-pa/nightly"

deploy(){
  spushd "$(get_git_root)/releaseScripts/default"
  new_dir="${DATE}-${ULT_VERSION}"
  echo "Deploying Ultimate ${ULT_VERSION} by moving *.zip via SFTP to ${RHOST}:${TARGET_DIR}/${new_dir}"
  sftp -oPort=$PORT -o StrictHostKeyChecking=no "${RUSER}@${RHOST}":${TARGET_DIR}/ <<< "mkdir ${new_dir}"
  for i in *.zip ; do
    sftp -oPort=$PORT -o StrictHostKeyChecking=no "${RUSER}@${RHOST}":"${TARGET_DIR}/${new_dir}" <<< "put ${i}"
  done
  spopd
}

get_ult_version
deploy
