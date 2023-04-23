#!/bin/bash
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

DATE=$(date +%Y%m%d)
RUSER="jenkins-deploy"
RHOST="struebli.informatik.uni-freiburg.de"

set_version(){
  spushd "$(get_git_root)/releaseScripts/default/UAutomizer-linux"
  VERSION=$(run_python Ultimate.py --ultversion)
  local rtr_code="$?"
  if ! [[ "$rtr_code" -eq "0" ]] ; then
    echo "./Ultimate.py --ultversion failed with $rtr_code"
    echo "Output was:"
    echo "$VERSION"
    exit $rtr_code
  fi
  VERSION=$(echo "$VERSION" | head -n 1 | sed 's/This is Ultimate //g ; s/origin.//g')
  if [ -z "$VERSION" ] ; then
    echo "Could not extract version string from './Ultimate.py --ultversion' output:"
    echo "$VERSION"
    exit 1
  fi
  spopd
}

deploy(){
  spushd "$(get_git_root)/releaseScripts/default"
  new_dir="${DATE}-${VERSION}"
  echo "Deploying Ultimate ${VERSION} by moving *.zip via SFTP to ${RHOST}:upload/${new_dir}"
  sftp -o StrictHostKeyChecking=no "${RUSER}@${RHOST}":upload/ <<< "mkdir ${new_dir}"
  for i in *.zip ; do
    sftp -o StrictHostKeyChecking=no "${RUSER}@${RHOST}":"upload/${new_dir}" <<< "put ${i}"
  done
  spopd
}

set_version
deploy
