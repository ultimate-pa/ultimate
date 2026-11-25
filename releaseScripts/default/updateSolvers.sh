#!/bin/bash
# Update external solvers except SMTInterpol

# Last installed version of each solver. Rewritten automatically by this
# script after every successful update; used by '--pinned' to reproduce
# exactly these versions.
PINNED_MATHSAT="5.6.17"
PINNED_CVC5="1.4.2"
PINNED_BITWUZLA="0.9.1"
PINNED_Z3="4.15.4"

readme_files=(
  "adds/README"
  "adds/gemcutter/README.md"
)

SCRIPT_PATH="$(cd "$(dirname "$0")" && pwd)/$(basename "$0")"

print_usage(){
  cat <<EOF
Usage: $(basename "$0") [solver] [options]

Update the external solvers in adds/solvers.

Solver (optional, default: all):
  mathsat|cvc5|bitwuzla|z3|all

Options:
  --latest                Update each selected solver to the latest available version (default)
  --pinned                Update each selected solver to the version pinned in this script (PINNED_<SOLVER>)
  --version SOLVER=X.Y.Z  Update SOLVER to the given version (repeatable; overrides the active mode for that solver)
  -h, --help              Show this help

After every successful update, the pin for that solver (PINNED_<SOLVER>) is rewritten in this script.
EOF
}

print_heading(){
  local solver="$1"
  local text="Updating ${solver}${target_version:+ (version $target_version)}"
  local separator
  separator="$(printf "%${#text}s" "" | tr ' ' '=')"
  echo "$separator"
  echo "$text"
  echo "$separator"
}

update_readme_version(){
  local solver="$1"
  local version="$2"
  local platform="${3:-}"
  local pattern="\($solver"
  if [ -n "$platform" ]; then
    pattern="$platform $pattern"
  fi
  for f in "${readme_files[@]}" ; do
    echo "$f"
    sed -z -E -i "s/(\n[ \t]*\*[^\n]*$pattern[^\n]*)\n([ \t]*)[^\n]*/\1\n\2$version/g" "$f"
  done
}

# Select the solver to update ('mathsat', 'cvc5', 'bitwuzla', 'z3' or 'all')
SELECTED_SOLVER="all"
MODE="latest"
declare -A VERSION_OVERRIDES=()

upper_case_solver(){
  echo "$1" | tr '[:lower:]' '[:upper:]'
}

# Resolve the version to install for a solver:
# explicit --version override, else the pin in pinned mode, else empty (= latest)
target_version_for(){
  local solver="$1"
  local override="${VERSION_OVERRIDES[$solver]:-}"
  if [ -n "$override" ]; then
    echo "$override"
    return
  fi
  if [ "$MODE" = "pinned" ]; then
    local var="PINNED_$(upper_case_solver "$solver")"
    echo "${!var}"
  fi
}

# jq expression selecting the release to download: the release whose tag
# contains the target version, or the latest release when no target is given
jq_release_selector(){
  local target="$1"
  if [ -n "$target" ]; then
    echo "map(select(.tag_name | contains(\"$target\"))) | first"
  else
    echo "first"
  fi
}

# Fetch all releases of a repository (following pagination) as a single JSON
# array; pages that fail or are not arrays (e.g. rate limit responses) are skipped
fetch_releases(){
  local repo="$1"
  local page=1
  local result="[]"
  while [ "$page" -le 10 ]; do
    local chunk
    chunk="$(curl -sL "https://api.github.com/repos/${repo}/releases?per_page=100&page=${page}")"
    local length
    length="$(echo "$chunk" | jq -r 'if type=="array" then length else 0 end' 2>/dev/null)" || length=0
    if [ -z "$length" ] || [ "$length" = "0" ]; then
      break
    fi
    result="$(echo "$result" "$chunk" | jq -s '.[0] + .[1]')"
    page=$((page+1))
  done
  echo "$result"
}

# Extract the bare version number (X.Y.Z) from a version string
bare_version(){
  printf '%s' "$1" | grep -oP '\d+\.\d+\.\d+' | head -n1
}

# Rewrite the pin variable for a solver in this script
update_pin(){
  local solver="$1"
  local version="$2"
  local var="PINNED_$(upper_case_solver "$solver")"
  if [ -z "$version" ]; then
    echo "Cannot update ${var}: no version number found"
    return 1
  fi
  if ! sed -i "s/^${var}=\"[^\"]*\"/${var}=\"${version}\"/" "$SCRIPT_PATH"; then
    echo "Failed to update ${var} in ${SCRIPT_PATH}"
    return 1
  fi
  echo "Updated ${var} in the script to ${version}"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    mathsat|cvc5|bitwuzla|z3|all)
      SELECTED_SOLVER="$1"
      ;;
    --latest|--pinned)
      if [ -n "${MODE_SET:-}" ] && [ "$MODE" != "${1#--}" ]; then
        echo "Cannot combine '--latest' and '--pinned'"
        exit 1
      fi
      MODE="${1#--}"
      MODE_SET=1
      ;;
    --version)
      shift
      if [ $# -eq 0 ]; then
        echo "Missing argument for '--version' -- expected SOLVER=X.Y.Z"
        exit 1
      fi
      override="$1"
      ;;
    --version=*)
      override="${1#--version=}"
      ;;
    -h|--help)
      print_usage
      exit 0
      ;;
    *)
      echo "Wrong argument: '${1}' -- use 'mathsat', 'cvc5', 'bitwuzla', 'z3' or 'all', see --help"
      exit 1
      ;;
  esac
  if [ -n "${override:-}" ]; then
    solver="${override%%=*}"
    version="${override#*=}"
    case "$solver" in
      mathsat|cvc5|bitwuzla|z3) ;;
      *)
        echo "Wrong solver in '--version ${override}' -- use 'mathsat', 'cvc5', 'bitwuzla' or 'z3'"
        exit 1
        ;;
    esac
    if [ "$solver" = "$version" ]; then
      echo "Missing version in '--version ${override}' -- expected SOLVER=X.Y.Z"
      exit 1
    fi
    if ! [[ "$version" =~ ^[A-Za-z0-9._-]+$ ]]; then
      echo "Invalid version in '--version ${override}' -- unexpected characters in '${version}'"
      exit 1
    fi
    VERSION_OVERRIDES["$solver"]="$version"
    unset override
  fi
  shift
done

## Mathsat
update_mathsat(){
  local target_version
  target_version="$(target_version_for mathsat)"
  if [ "$MODE" = "pinned" ] && [ -z "$target_version" ]; then
    echo "No pinned version for mathsat (PINNED_MATHSAT is empty)"
    return 1
  fi
  print_heading "mathsat"
  TMP_DIR="mathsat"
  local downloads
  downloads="$(curl -sL https://mathsat.fbk.eu/download.html |grep -oP "href=\"\K.*(linux-x86_64*.tar.gz|linux-aarch64*.tar.gz|macos*.tar.gz|-win64*.zip)\"" | sed 's:"::g')"
  if [ -n "$target_version" ]; then
    local filtered
    filtered="$(echo "$downloads" | grep -- "$target_version")"
    if [ -z "$filtered" ]; then
      # Old versions are not listed on the website but remain available under
      # the same release URL scheme; derive their URLs from the latest ones.
      filtered="$(echo "$downloads" | sed "s/mathsat-[0-9][0-9.]*/mathsat-${target_version}/g")"
      local checked=""
      while IFS='' read -r url ; do
        [ -z "$url" ] && continue
        if [ "$(curl -s -o /dev/null -w '%{http_code}' -I "https://mathsat.fbk.eu/$url")" = "200" ]; then
          if [ -z "$checked" ]; then checked="$url"; else checked+=$'\n'"$url"; fi
        else
          echo "No mathsat download found at https://mathsat.fbk.eu/$url"
        fi
      done <<< "$filtered"
      filtered="$checked"
    fi
    downloads="$filtered"
    if [ -z "$downloads" ]; then
      echo "No mathsat download found for version ${target_version}"
      return 1
    fi
  fi
  local updated_linux=0 updated_macos=0 updated_windows=0
  while IFS='' read -r l ; do
    mkdir "$TMP_DIR"
    filename="$(echo "$l" | grep -oP "mathsat.*")"
    echo "Updating $filename"
    curl -sL -o "$filename" "https://mathsat.fbk.eu/$l"
    if [[ "$filename" == *tar.gz ]]; then
      tar xzf "$filename" -C "$TMP_DIR"
      if [[ "$filename" == *linux-x86_64* ]]; then
        targets=("linux/x86_64")
        updated_linux=1
      elif [[ "$filename" == *linux-aarch64* ]]; then
        targets=("linux/aarch64")
        updated_linux=1
      elif [[ "$filename" == *macos* ]]; then
        targets=("macosx/x86_64" "macosx/aarch64")
        updated_macos=1
      else
        echo "Don't know what to do with $filename"
        rm -r "$TMP_DIR"
        continue
      fi
      for target in "${targets[@]}" ; do
        find "$TMP_DIR" -type f -name mathsat -exec cp "{}" "adds/solvers/$target/" \;
        chmod a+x "adds/solvers/$target/mathsat"
      done
      find "$TMP_DIR" -type f -name LICENSE.txt -exec cp "{}" adds/licenses/mathsat-LICENSE \;
    elif [[ "$filename" == *zip ]]; then
      unzip -q -o -d "$TMP_DIR" "$filename"
      find "$TMP_DIR" \( -type f -name mathsat.exe -or -wholename '*/bin/*.dll' \) -exec cp "{}" "adds/solvers/win32/x86_64/" \;
      chmod a+x "adds/solvers/win32/x86_64/mathsat.exe"
      find "$TMP_DIR" -type f -name LICENSE.txt -exec cp "{}" adds/licenses/mathsat-LICENSE \;
      updated_windows=1
    else
      echo "Don't know what to do with $filename"
      rm -r "$TMP_DIR"
      continue
    fi
    rm -r "$TMP_DIR"
  done <<< "$downloads"
  if [ "$updated_linux" = 0 ] && [ "$updated_macos" = 0 ] && [ "$updated_windows" = 0 ]; then
    echo "No mathsat files were updated"
    return 1
  fi
  # Read the full version output from the installed x86_64 binary and use it
  # for the README of every platform
  version="$(adds/solvers/linux/x86_64/mathsat -version)"
  echo "$version"
  mathsat_version="$(bare_version "$version")"
  if [ -z "$mathsat_version" ]; then
    echo "Failed to determine the mathsat version by executing the solver"
    return 1
  fi
  if [ "$updated_linux" = 1 ]; then
    update_readme_version mathsat "$version" "Linux"
  fi
  if [ "$updated_macos" = 1 ]; then
    update_readme_version mathsat "$version" "MacOS"
  fi
  if [ "$updated_windows" = 1 ]; then
    update_readme_version mathsat "$version" "Windows"
  fi
  if [ -n "$target_version" ]; then
    update_pin mathsat "$target_version"
  else
    update_pin mathsat "$mathsat_version"
  fi
}

## cvc5
update_cvc5(){
  local target_version
  target_version="$(target_version_for cvc5)"
  if [ "$MODE" = "pinned" ] && [ -z "$target_version" ]; then
    echo "No pinned version for cvc5 (PINNED_CVC5 is empty)"
    return 1
  fi
  print_heading "cvc5"
  local release_selector
  release_selector="$(jq_release_selector "$target_version")"
  local releases
  releases="$(fetch_releases cvc5/cvc5)"
  TMP_DIR="cvc5"
  TMP_ZIP="$TMP_DIR/cvc5.zip"
  for platform in Linux-x86_64 Linux-arm64 macOS-x86_64 macOS-arm64 Win64-x86_64 ; do
    nightly=$(echo "$releases" | jq -r 'map(select(.prerelease|not)) | '"$release_selector"' | (.assets // [])[] | select (.name| test("cvc5-'$platform'-static\\.zip")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $nightly"
    if [ -z "$nightly" ]; then
      echo "No cvc5 build found for ${platform}${target_version:+ (version $target_version)}"
      return 1
    fi

    mkdir "$TMP_DIR"
    curl -sL -o "$TMP_ZIP" "$nightly"
    unzip -q -o -d "$TMP_DIR" "$TMP_ZIP"
    case "$platform" in
      Linux-x86_64)
        target="cvc5"
        os="linux"
        arch="x86_64"
        ;;
      Linux-arm64)
        target="cvc5"
        os="linux"
        arch="aarch64"
        ;;
      macOS-x86_64)
        target="cvc5"
        os="macosx"
        arch="x86_64"
        ;;
      macOS-arm64)
        target="cvc5"
        os="macosx"
        arch="aarch64"
        ;;
      Win64-x86_64)
        target="cvc5.exe"
        os="win32"
        arch="x86_64"
        ;;
    esac
    find "$TMP_DIR" -type f -name $target -exec cp "{}" "adds/solvers/$os/$arch/" \;
    chmod a+x "adds/solvers/$os/$arch/$target"
    rm -r "$TMP_DIR"
  done
  curl -sL -o adds/licenses/cvc5-LICENSE https://raw.githubusercontent.com/cvc5/cvc5/main/COPYING
  version="$(adds/solvers/linux/x86_64/cvc5 -V | head -n1)"
  echo "$version"
  readme_version="$(bare_version "$version")"
  if [ -z "$readme_version" ]; then
    echo "Failed to determine the cvc5 version by executing the solver"
    return 1
  fi
  update_readme_version cvc5 "$version"
  if [ -n "$target_version" ]; then
    update_pin cvc5 "$target_version"
  else
    update_pin cvc5 "$readme_version"
  fi
}

## bitwuzla
update_bitwuzla(){
  local target_version
  target_version="$(target_version_for bitwuzla)"
  if [ "$MODE" = "pinned" ] && [ -z "$target_version" ]; then
    echo "No pinned version for bitwuzla (PINNED_BITWUZLA is empty)"
    return 1
  fi
  print_heading "bitwuzla"
  local release_selector
  release_selector="$(jq_release_selector "$target_version")"
  local releases
  releases="$(fetch_releases bitwuzla/bitwuzla)"
  TMP_DIR="bitwuzla"
  TMP_ZIP="$TMP_DIR/bitwuzla.zip"
  for platform in Linux-x86_64 Linux-arm64 macOS-arm64 Win64-x86_64 ; do
    build=$(echo "$releases" | jq -r ''"$release_selector"' | (.assets // [])[] | select (.name| test("Bitwuzla-'$platform'-static(-latest)?\\.zip")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $build"
    if [ -z "$build" ]; then
      echo "No bitwuzla build found for ${platform}${target_version:+ (version $target_version)}"
      return 1
    fi

    mkdir "$TMP_DIR"
    curl -sL -o "$TMP_ZIP" "$build"
    unzip -q -o -d "$TMP_DIR" "$TMP_ZIP"
    case "$platform" in
      Linux-x86_64)
        target="bitwuzla"
        os="linux"
        arch="x86_64"
        ;;
      Linux-arm64)
        target="bitwuzla"
        os="linux"
        arch="aarch64"
        ;;
      macOS-arm64)
        target="bitwuzla"
        os="macosx"
        arch="aarch64"
        ;;
      Win64-x86_64)
        target="bitwuzla.exe"
        os="win32"
        arch="x86_64"
        ;;
    esac
    find "$TMP_DIR" -type f -name $target -exec cp "{}" "adds/solvers/$os/$arch/" \;
    chmod a+x "adds/solvers/$os/$arch/$target"
    rm -r "$TMP_DIR"
  done
  curl -sL -o adds/licenses/bitwuzla-LICENSE https://raw.githubusercontent.com/bitwuzla/bitwuzla/main/COPYING
  version="$(adds/solvers/linux/x86_64/bitwuzla -V)"
  echo "$version"
  readme_version="$(bare_version "$version")"
  if [ -z "$readme_version" ]; then
    echo "Failed to determine the bitwuzla version by executing the solver"
    return 1
  fi
  update_readme_version bitwuzla "Bitwuzla version $readme_version"
  if [ -n "$target_version" ]; then
    update_pin bitwuzla "$target_version"
  else
    update_pin bitwuzla "$readme_version"
  fi
}

## z3
update_z3(){
  local target_version
  target_version="$(target_version_for z3)"
  if [ "$MODE" = "pinned" ] && [ -z "$target_version" ]; then
    echo "No pinned version for z3 (PINNED_Z3 is empty)"
    return 1
  fi
  print_heading "z3"
  local release_selector
  release_selector="$(jq_release_selector "$target_version")"
  local releases
  releases="$(fetch_releases Z3Prover/z3)"
  TMP_DIR="z3"
  TMP_ZIP="$TMP_DIR/z3.zip"
  for platform in x64-glibc x64-osx arm64-osx arm64-glibc ; do
    build=$(echo "$releases" | jq -r 'map(select(.prerelease|not)) | '"$release_selector"' | (.assets // [])[] | select (.name| test("z3-.*-'$platform'-.*\\.zip")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $build"
    if [ -z "$build" ]; then
      echo "No z3 build found for ${platform}${target_version:+ (version $target_version)}"
      return 1
    fi

    mkdir "$TMP_DIR"
    curl -sL -o "$TMP_ZIP" "$build"
    unzip -q -o -d "$TMP_DIR" "$TMP_ZIP"
    case "$platform" in
      x64-glibc)
        os="linux"
        arch="x86_64"
        ;;
      x64-osx)
        os="macosx"
        arch="x86_64"
        ;;
      arm64-osx)
        os="macosx"
        arch="aarch64"
        ;;
      arm64-glibc)
        os="linux"
        arch="aarch64"
        ;;
    esac
    find "$TMP_DIR" -type f -name z3 -exec cp "{}" "adds/solvers/$os/$arch/" \;
    chmod a+x "adds/solvers/$os/$arch/z3"
    find "$TMP_DIR" -type f -name LICENSE.txt -exec cp "{}" adds/licenses/z3-LICENSE \;
    rm -r "$TMP_DIR"
  done
  version="$(adds/solvers/linux/x86_64/z3 --version)"
  echo "$version"
  readme_version="$(bare_version "$version")"
  if [ -z "$readme_version" ]; then
    echo "Failed to determine the z3 version by executing the solver"
    return 1
  fi
  update_readme_version z3 "$version"
  if [ -n "$target_version" ]; then
    update_pin z3 "$target_version"
  else
    update_pin z3 "$readme_version"
  fi
}

case "${SELECTED_SOLVER}" in
  mathsat)
    update_mathsat
    ;;
  cvc5)
    update_cvc5
    ;;
  bitwuzla)
    update_bitwuzla
    ;;
  z3)
    update_z3
    ;;
  all)
    update_mathsat
    update_cvc5
    update_bitwuzla
    update_z3
    ;;
esac
