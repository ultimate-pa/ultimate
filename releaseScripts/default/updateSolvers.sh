#!/bin/bash
# Update external solvers except SMTInterpol

readme_files=(
  "adds/README"
  "adds/gemcutter/README.md"
)

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
SELECTED_SOLVER="${1:-all}"
case "${SELECTED_SOLVER}" in
  mathsat|cvc5|bitwuzla|z3|all) ;;
  *)
    echo "Wrong argument: '${SELECTED_SOLVER}' -- use 'mathsat', 'cvc5', 'bitwuzla', 'z3' or 'all'"
    exit 1
    ;;
esac

## Mathsat
update_mathsat(){
  TMP_DIR="mathsat"
  while IFS='' read -r l ; do
    mkdir "$TMP_DIR"
    filename="$(echo "$l" | grep -oP "mathsat.*")"
    echo "Updating $filename"
    curl -sL -o "$filename" "https://mathsat.fbk.eu/$l"
    if [[ "$filename" == *tar.gz ]]; then
      tar xzf "$filename" -C "$TMP_DIR"
      if [[ "$filename" == *linux-x86_64* ]]; then
        platform="Linux"
        targets=("linux/x86_64")
        version="$(adds/solvers/linux/x86_64/mathsat -version)"
      elif [[ "$filename" == *linux-aarch64* ]]; then
        platform="Linux"
        targets=("linux/aarch64")
        version="MathSAT5 version $(echo "$filename" | grep -oP "\d+\.\d+\.\d+")"
      elif [[ "$filename" == *macos* ]]; then
        platform="MacOS"
        targets=("macosx/x86_64" "macosx/aarch64")
        version="MathSAT5 version $(echo "$filename" | grep -oP "\d+\.\d+\.\d+")"
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
      platform="Windows"
      os="win32"
      unzip -q -o -d "$TMP_DIR" "$filename"
      find "$TMP_DIR" \( -type f -name mathsat.exe -or -wholename '*/bin/*.dll' \) -exec cp "{}" "adds/solvers/$os/x86_64/" \;
      chmod a+x "adds/solvers/$os/x86_64/mathsat.exe"
      find "$TMP_DIR" -type f -name LICENSE.txt -exec cp "{}" adds/licenses/mathsat-LICENSE \;
      version="MathSAT5 version $(echo "$filename" | grep -oP "\d+\.\d+\.\d+")"
    else
      echo "Don't know what to do with $filename"
      rm -r "$TMP_DIR"
      continue
    fi
    rm -r "$TMP_DIR"
    if [ -z "$version" ] || [ -z "$platform" ]; then
      echo "Could not extract version or platform for $filename"
      continue
    fi
    echo "$version"
    update_readme_version mathsat "$version" "$platform"
  done < <(curl -sL https://mathsat.fbk.eu/download.html |grep -oP "href=\"\K.*(linux-x86_64*.tar.gz|linux-aarch64*.tar.gz|macos*.tar.gz|-win64*.zip)\"" | sed 's:"::g')
}

## cvc5
update_cvc5(){
  TMP_DIR="cvc5"
  TMP_ZIP="$TMP_DIR/cvc5.zip"
  for platform in Linux-x86_64 Linux-arm64 macOS-x86_64 macOS-arm64 Win64-x86_64 ; do
    nightly=$(curl -sL https://api.github.com/repos/cvc5/cvc5/releases | jq -r 'map(select(.prerelease|not)) | first | .assets[] | select (.name| test("cvc5-'$platform'-static\\.zip")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $nightly"

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
  update_readme_version cvc5 "$version"
}

## bitwuzla
update_bitwuzla(){
  TMP_DIR="bitwuzla"
  TMP_ZIP="$TMP_DIR/bitwuzla.zip"
  for platform in Linux-x86_64 Linux-arm64 macOS-arm64 Win64-x86_64 ; do
    build=$(curl -sL https://api.github.com/repos/bitwuzla/bitwuzla/releases | jq -r 'first | .assets[] | select (.name| test("Bitwuzla-'$platform'-static(-latest)?\\.zip")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $build"

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
  update_readme_version bitwuzla "$version"
}

## z3
update_z3(){
  TMP_DIR="z3"
  TMP_ZIP="$TMP_DIR/z3.zip"
  for platform in x64-osx arm64-osx arm64-glibc ; do
    build=$(curl -sL https://api.github.com/repos/Z3Prover/z3/releases | jq -r 'map(select(.prerelease|not)) | first | .assets[] | select (.name| test("z3-.*-'$platform'-.*\\.zip")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $build"

    mkdir "$TMP_DIR"
    curl -sL -o "$TMP_ZIP" "$build"
    unzip -q -o -d "$TMP_DIR" "$TMP_ZIP"
    case "$platform" in
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
  update_readme_version z3 "$version"
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