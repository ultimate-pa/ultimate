#!/bin/bash
# Update external solvers except SMTInterpol

readme_files=(
  "adds/README"
  "adds/gemcutter/README.md"
  "adds/reqchecker/README"
)

## Mathsat
update_mathsat(){
  TMP_DIR="mathsat"
  while IFS='' read -r l ; do
    mkdir "$TMP_DIR"
    filename=$(echo "$l" | grep -oP "mathsat.*")
    echo "Updating $filename"
    curl -sL -o "$filename" "https://mathsat.fbk.eu/$l"
    if [[ "$filename" == *tar.gz ]]; then
      tar xzf "$filename" -C "$TMP_DIR"
      find "$TMP_DIR" -type f -name mathsat -exec cp "{}" adds/ \;
      chmod a+x adds/mathsat
      version=$(adds/mathsat -version)
      platform="Linux"
    elif [[ "$filename" == *zip ]]; then
      unzip -q -o -d "$TMP_DIR" "$filename"
      find "$TMP_DIR" \( -type f -name mathsat.exe -or -wholename '*/bin/mathsat.dll' -or -wholename '*/bin/mpir.dll' \) -exec cp "{}" adds/ \;
      chmod a+x adds/mathsat.exe
      version=$(echo "$filename" | grep -oP "\d+\.\d+\.\d+")
      platform="Windows"
    else
      echo "Don't know what to do with $filename"
      continue
    fi
    rm -r "$TMP_DIR"
    if [ -z "$version" ] || [ -z "$platform" ]; then 
      echo "Could not extract version or platform for $filename"
      continue
    fi
    for f in "${readme_files[@]}" ; do
      echo "$f"
      sed -z -E -i "s/($platform \(mathsat[^\n]*)\n(\s*)[^\n]*/\1\n\2$version/g" "$f"
    done
  done < <(curl -sL https://mathsat.fbk.eu/download.html |grep -oP "href=\"\K.*(linux-x86_64-reentrant.tar.gz|-win64-msvc.zip)\"" | sed 's:"::g')
}

## cvc5
update_cvc5(){
  for platform in Linux Win64 ; do 
    nightly=$(curl -sL https://api.github.com/repos/cvc5/cvc5/releases | jq -r 'map(select(.prerelease)) | first | .assets[] | select (.name| test(".*'$platform'.*$")) | .browser_download_url' | sort | tail -n1)
    echo "$platform $nightly"
    
    if [[ "$platform" == "Linux" ]]; then
      target="adds/cvc5"
    else
      target="adds/cvc5.exe"
    fi
    curl -sL -o "$target" "$nightly"
    chmod a+x "$target"
  done
  curl -sL -o adds/cvc5-LICENSE https://raw.githubusercontent.com/cvc5/cvc5/main/COPYING
  version=$(adds/cvc5 -V | head -n1 | tr '\n' ' ' | sed 's/This is //g')
  version+="from ""$(echo "$nightly" | grep -oP "\-\d+\-\d+\-\d+\-\K.*" | sed 's/.exe//g')"
  echo "$version"
}
update_cvc5

# TODO: continue when the rate limit allows us again (its 50 per h for unauthenticated users)