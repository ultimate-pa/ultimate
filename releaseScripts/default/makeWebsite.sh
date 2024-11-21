#!/bin/bash
# Script that builds the static website for Ultimate using Jekyll. 
# It expects that Ultimate was already build with makeFresh.sh.
# If you want to deploy the website, use deploy_website.sh after makeWebsite.sh.

# load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

root="$(get_git_root)"
website_static_dir="${root}/trunk/source/WebsiteStatic"
relscripts="${root}/releaseScripts/default"
target_dir="${relscripts}/WebFrontend"

if is_linux ; then
  ultdir="UAutomizer-linux"
elif is_windows ; then
  ultdir="UAutomizer-win32"
else
  echo "Unsupported OS type $OSTYPE"
  exit 1
fi

ultdir=$(readlink -f "${relscripts}/${ultdir}")
if ! [ -d "$ultdir" ]; then
  echo "Could not find $ultdir"
  exit 1
fi

export PATH="${PATH}:${ultdir}"
spushd "$website_static_dir"
# this step will create the diretory _site
exit_on_fail bundle install 
exit_on_fail run_python scripts/build.py --production
spopd
if [ -d "$target_dir" ]; then
  rm -r "$target_dir"
fi
echo "Moving ${website_static_dir}/_site to $target_dir"
mv "${website_static_dir}/_site" "$target_dir"
echo "$target_dir"
ls -al "$target_dir"
