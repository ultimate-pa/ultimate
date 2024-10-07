#!/bin/bash
# Deploy the website to our local server. 
# Requires the website to be built first.

# load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

RHOST="sopra-docker"
TARGET_DIR="/mnt/shared/ultimate-pa"

deploy(){
  spushd "$(get_git_root)/releaseScripts/default"
  echo "Deploying Ultimate ${ULT_VERSION} website to ${TARGET_DIR} on ${RHOST}"

  echo "${ULT_VERSION}" > WEBSITE_VERSION
  if diff -q <(ssh -q "$RHOST" -- "cat ${TARGET_DIR}/VERSION || echo unknown") WEBSITE_VERSION ; then
    echo "Already on this version, skipping"
    exit 1
  fi

  echo "Stopping Ultimate website"
  exit_on_fail ssh ${RHOST} -- "cd /srv/infrastructure/deployments/ultimate-pa ; docker-compose down"
  
  echo "Removing old website"
  ssh ${RHOST} bash <<EOF
  rm -r ${TARGET_DIR}/backend
  mkdir ${TARGET_DIR}/backend
  rm -r ${TARGET_DIR}/frontend
  mkdir ${TARGET_DIR}/frontend
  rm -r ${TARGET_DIR}/config
  mkdir ${TARGET_DIR}/config
EOF

  echo "Copying new website"
  sftp -o StrictHostKeyChecking=no "${RHOST}" -b <<EOF
  put -r WebBackend/* ${TARGET_DIR}/backend/
  put -r WebFrontend/* ${TARGET_DIR}/frontend/
  put -r ../website-config/* ${TARGET_DIR}/config/
  put adds/z3 ${TARGET_DIR}/solver/
  put adds/cvc5 ${TARGET_DIR}/solver/
  put adds/mathsat ${TARGET_DIR}/solver/
  put adds/ltl2ba ${TARGET_DIR}/solver/
  put WEBSITE_VERSION ${TARGET_DIR}/VERSION
EOF
  rm WEBSITE_VERSION

  echo "Starting Ultimate website"
  exit_on_fail ssh "root@${RHOST}" -- "cd /srv/infrastructure/deployments/ultimate-pa ; docker-compose up -d"

  spopd
}

spushd "$DIR"
get_ult_version # will populate ULT_VERSION
deploy




