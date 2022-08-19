#!/bin/bash
DATE=$(date +%Y%m%d)
pushd releaseScripts/default > /dev/null
pushd UAutomizer-linux > /dev/null
VERSION=$(./Ultimate.py --ultversion)
if [ $? -ne 0 ] ; then 
  echo "Ultimate did not provide a version"
  exit 1
fi
VERSION=$(echo "$VERSION" | head -n 1 | sed 's/This is Ultimate //g ; s/origin.//g')
if [ -z "$VERSION" ] ; then 
  echo "Ultimate did not provide a version"
  exit 1
fi
popd > /dev/null

new_dir="${DATE}-${VERSION}"
echo "Deploying Ultimate ${VERSION} by moving *.zip via SFTP to struebli.informatik.uni-freiburg.de:upload/${new_dir}"
sftp -o StrictHostKeyChecking=no jenkins-deploy@struebli.informatik.uni-freiburg.de:upload/ <<< "mkdir ${new_dir}"
for i in *.zip ; do
  sftp -o StrictHostKeyChecking=no jenkins-deploy@struebli.informatik.uni-freiburg.de:upload/${new_dir} <<< "put ${i}"
done

