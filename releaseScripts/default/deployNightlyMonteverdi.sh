#!/bin/bash -ex
# We do not call this script directly, but use it to track changes to the script used in Jenkins 

DATE=$(date +%Y%m%d)
DEPLOY_DIR="/var/www/localhost/htdocs/ultimate-nightly"
cd releaseScripts/default
#./makeFresh.sh
pushd UAutomizer-linux > /dev/null
VERSION=$(./Ultimate.py --ultversion | head -n 1 | sed 's/This is Ultimate //g')
TARGET="${DEPLOY_DIR}/${DATE}-${VERSION}"
popd > /dev/null
mkdir "${TARGET}"
mv *.zip "${TARGET}/"
find "${DEPLOY_DIR}" -type d -ctime +7 -exec rm -r {} \;
