#!/bin/bash
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"


RHOST="sopra-docker"
TARGET_DIR="/mnt/shared/ultimate-pa"

# current structure is
# backend
# config/
# ├── backend
# │   ├── settings_whitelist.json
# │   ├── WebBackend.ini
# │   └── web.config.properties
# ├── frontend
# │   └── config.js
# └── nginx
#     ├── conf.d
#     │   └── default.conf
#     └── nginx.conf
# frontend
# solver
# ├── cvc4
# ├── ltl2ba
# ├── mathsat
# └── z3

deploy(){
  # TODO improve perhaps using rsync instead of sftp 
  spushd "$(get_git_root)/releaseScripts/default"
  echo "Deploying Ultimate ${ULT_VERSION} to ${TARGET_DIR} on ${RHOST}"

  echo "${ULT_VERSION}" > WEBSITE_VERSION
  if diff -q <(ssh -q "$RHOST" -- "cat ${TARGET_DIR}/VERSION || echo unknown") WEBSITE_VERSION ; then
    echo "Already on this version, skipping"
    exit 1
  fi
  sftp -o StrictHostKeyChecking=no "${RHOST}" -b <<EOF
  rm ${TARGET_DIR}/backend
  mkdir ${TARGET_DIR}/backend
  put -r WebBackend/* ${TARGET_DIR}/backend/
  rm ${TARGET_DIR}/frontend
  mkdir ${TARGET_DIR}/frontend
  put -r WebFrontend/* ${TARGET_DIR}/frontend/
  rm ${TARGET_DIR}/config
  mkdir ${TARGET_DIR}/config
  put -r ../website-config/* ${TARGET_DIR}/config/
  put adds/z3 ${TARGET_DIR}/solver/
  put adds/cvc4 ${TARGET_DIR}/solver/
  put adds/mathsat ${TARGET_DIR}/solver/
  put adds/ltl2ba ${TARGET_DIR}/solver/
  put WEBSITE_VERSION ${TARGET_DIR}/VERSION
EOF
  rm WEBSITE_VERSION
  spopd
}

get_ult_version
deploy




