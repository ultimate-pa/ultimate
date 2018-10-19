#!/bin/bash

SVCOMP_GITLAB_DIR=/storage/repos/svcomp-archives-2019/2019
POST_FINAL=false

EXPECTED_FILES=(
"UltimateAutomizer-linux.zip"
"UltimateKojak-linux.zip"
"UltimateTaipan-linux.zip"
)

VALIDATOR="uautomizer.zip"
VALIDATOR_SYMLINK="val_uautomizer.zip"

function git_is_clean {
    git diff-index --quiet HEAD --
}

if [ ! -d "$SVCOMP_GITLAB_DIR" ]; then 
	echo "Directory $SVCOMP_GITLAB_DIR does not exist"
	exit 1
fi

pushd "$SVCOMP_GITLAB_DIR" > /dev/null
if ! git_is_clean ; then 
	echo "Repo is dirty, did you do things manually?"
	exit 1
fi

current_branch=`git rev-parse --abbrev-ref HEAD`
if [ "ultimate" != "$current_branch" ]; then
	echo "Repo is in wrong branch: $current_branch"
	exit 1
fi

echo "Updating..."
git fetch --all
git rebase
git rebase master
git push
popd > /dev/null


VERSION=`git describe --tags $(git rev-list --tags --max-count=1)`
VERSION="${VERSION}-"`git rev-parse HEAD | cut -c1-8`

echo "Copying .zip files for version $VERSION to SVCOMP 2019 GitLab repo in $SVCOMP_GITLAB_DIR"
for z in "${EXPECTED_FILES[@]}"; do
    if [ ! -f $z ]; then
		echo "$z does not exist"
		exit 1
	fi
    f=$(echo $z | sed 's/Ultimate\(.*\)-linux\.zip/u\1\.zip/g' | tr '[:upper:]' '[:lower:]')
	if $POST_FINAL ; then
		f="${f%.zip}-post-final.zip"
	fi
    echo "Copying $z to ${SVCOMP_GITLAB_DIR}/${f}"
	cp "$z" "${SVCOMP_GITLAB_DIR}/${f}"
done

pushd "$SVCOMP_GITLAB_DIR" > /dev/null

if [ ! -L "${SVCOMP_GITLAB_DIR}/${VALIDATOR_SYMLINK}" ]; then
	ln -s "$VALIDATOR" "$VALIDATOR_SYMLINK"
fi

echo "Pushing to remote Ultimate"
git add -A
git commit -a -m"Update Ultimate tool family to version $VERSION"
git push

echo "Now file a pull request and wait for its acceptance!"
popd > /dev/null
