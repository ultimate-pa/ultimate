#!/bin/bash
# Script that deploys a new version to SVCOMP 23. You have to call makeFresh.sh before.

SVCOMP_GITLAB_ROOT="/storage/repos/svcomp-archives-2023"
SVCOMP_GITLAB_DIR="$SVCOMP_GITLAB_ROOT/2023"
SVCOMP_COVERITEAM_DIR="/storage/repos/coveriteam-trusted-ultimate"
SVCOMP_REMOTE_GIT="git@gitlab.com:sosy-lab/sv-comp/archives-2023.git"
# SVCOMP_REMOTE_GIT="git@gitlab.com:danieldietsch/archives-2023.git"
POST_FINAL=false

EXPECTED_FILES=(
"UltimateAutomizer-linux.zip"
"UltimateKojak-linux.zip"
"UltimateTaipan-linux.zip"
"UltimateGemCutter-linux.zip"
)

VALIDATOR="uautomizer.zip"
VALIDATOR_SYMLINK="val_uautomizer.zip"
VERSION=$(git describe --tags "$(git for-each-ref refs/tags/v* --sort=-creatordate --format='%(objectname)' --count=1)")
VERSION="${VERSION}-"$(git rev-parse HEAD | cut -c1-8)

git_is_clean() {
  git diff-index --quiet HEAD --
}

push_dir() {
  pushd "$1" > /dev/null || { echo "Could not switch to directory $1" ; exit 1 ; }
}

pop_dir() {
popd > /dev/null || { echo "Could not exit directory $PWD" ; exit 1 ; }
}

prepare_repo() {
  if [ ! -d "$1" ]; then
    echo "Directory $1 does not exist"
    exit 1
  fi
  push_dir "$1"
  if ! git_is_clean ; then
    echo "Repo $1 is dirty, did you do things manually?"
    exit 1
  fi

  echo "Updating..."
  git fetch --all
  if git ls-remote --exit-code upstream > /dev/null 2>&1 ; then
    git reset --hard upstream/main
  else
    git reset --hard origin/main
  fi
  pop_dir
}

prepare_svcomp_repo_shallow() {
  if [ ! -d "$1" ]; then
    echo "Directory $1 does not exist"
    exit 1
  fi
  rm -rf "$1"
  git clone --filter=blob:none --no-checkout "$SVCOMP_REMOTE_GIT" "$1"
  push_dir "$1"
  git sparse-checkout set --no-cone /2023/uautomizer.zip /2023/utaipan.zip /2023/ukojak.zip /2023/ugemcutter.zip /2023/val_uautomizer.zip
  git switch -c ultimate
  git checkout 
  pop_dir
}

copy_zips() {
  echo "Copying .zip files for version $VERSION to SVCOMP GitLab repo in $1"
  for z in "${EXPECTED_FILES[@]}"; do
      if [ ! -f "$z" ]; then
      echo "$z does not exist"
      exit 1
    fi
      f=$(echo "$z" | sed 's/Ultimate\(.*\)-linux\.zip/u\1\.zip/g' | tr '[:upper:]' '[:lower:]')
    if $POST_FINAL ; then
      f="${f%.zip}-post-final.zip"
    fi

    local_checksum=$(sha256sum "$z" | awk '{print $1}')
    if echo "$local_checksum ${1}/${f}" | sha256sum --check --status ; then
      echo "Same file already at ${1}/${f}, aborting"
      # return 1
    fi
    echo "Copying $z to ${1}/${f}"
    cp "$z" "${1}/${f}"
  done
  return 0
}

create_validator_symlinks() {
  push_dir "$SVCOMP_GITLAB_DIR"
  if [ ! -L "${1}/${VALIDATOR_SYMLINK}" ]; then
    ln -s "$VALIDATOR" "$VALIDATOR_SYMLINK"
  fi
  pop_dir
}

git_commit() {
  push_dir "$1"
  echo "Pushing to remote "
  git add -A
  local title="Update Ultimate tool family (uautomizer, ukojak, utaipan, ugemcutter) to version $VERSION"
  git commit -a -m"${title}"
  pop_dir
}

prepare_svcomp_repo_shallow "$SVCOMP_GITLAB_ROOT"
if copy_zips "$SVCOMP_GITLAB_DIR" ; then
  create_validator_symlinks "$SVCOMP_GITLAB_DIR"
  git_commit "$SVCOMP_GITLAB_DIR"
  push_dir "$SVCOMP_GITLAB_DIR"
  git push origin ultimate
  pop_dir
  echo "Now file a pull request and wait for its acceptance!"
fi

prepare_repo "$SVCOMP_COVERITEAM_DIR"
if copy_zips "$SVCOMP_COVERITEAM_DIR"; then
  git_commit "$SVCOMP_COVERITEAM_DIR"
    push_dir "$SVCOMP_COVERITEAM_DIR"
    git push -f
    pop_dir
fi