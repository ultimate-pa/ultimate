#!/bin/bash
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

DATE=$(date +%Y%m%d)

spushd "$(get_git_root)/releaseScripts/default/UAutomizer-linux"
if ! VERSION=$(./Ultimate.py --ultversion) ; then
  echo "./Ultimate.py --ultversion failed with $?"
  exit 1
fi
VERSION=$(echo "$VERSION" | head -n 1 | sed 's/This is Ultimate //g ; s/origin.//g')
if [ -z "$VERSION" ] ; then
  echo "Could not extract version string from './Ultimate.py --ultversion' output:"
  echo "$VERSION"
  exit 1
fi
spopd

new_dir="${DATE}-${VERSION}"
echo "Deploying Ultimate ${VERSION} by moving *.zip via SFTP to struebli.informatik.uni-freiburg.de:upload/${new_dir}"
sftp -o StrictHostKeyChecking=no jenkins-deploy@struebli.informatik.uni-freiburg.de:upload/ <<< "mkdir ${new_dir}"
for i in *.zip ; do
  sftp -o StrictHostKeyChecking=no jenkins-deploy@struebli.informatik.uni-freiburg.de:upload/${new_dir} <<< "put ${i}"
done

