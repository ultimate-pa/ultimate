#!/bin/bash
# This script generates a zip file for each Ultimate tool that should be deployed to GitHub or to some place else
# It takes additional binaries from the adds/ folder. Currently, we use z3, cvc5 and mathsat
# It also adds README, Ultimate.py, and various license files 



## include the makeSettings shared functions 
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"


## start the actual script 
if [ $# -le 2 ]; then
  echo "Not enough arguments supplied -- use arguments in the following order"
  echo "1. the toolname" 
  echo "2. 'linux' or 'win32' for the target platform"
  echo "3. (optional) the reach toolchain (e.g., 'AutomizerC_WitnessPrinter.xml')"
  echo "4. (optional) the termination toolchain or NONE"
  echo "5. (optional) the witness validation toolchain or NONE"
  echo "6. (optional) the memsafety deref and memtrack toolchain or NONE"
  echo "7. (optional) the ltl toolchain or NONE"
  echo "8. (optional) the termination witness validation toolchain or NONE"
  exit 1
fi

TOOLNAME="$1"
if [ -z "$TOOLNAME" ]; then
  echo "First argument (toolname) cannot be empty"
  exit 1
fi
LCTOOLNAME="$(echo "$TOOLNAME" | tr '[A-Z]' '[a-z]')"
echo "Using $TOOLNAME ($LCTOOLNAME) as toolname"


# additional files for all architectures 
ADDS=(
  "adds/LICENSE*"
  "adds/*LICENSE"
  "adds/Ultimate.py"
  "adds/Ultimate.ini"
  "adds/README"
)

# architecture-specific variables  
if [ "$2" == "linux" ]; then
  echo "Building .zip for linux..."
  ARCH="linux"
  ARCHPATH="products/CLI-E4/linux/gtk/x86_64"
  ADDS+=("adds/z3" "adds/cvc5" "adds/mathsat")
elif [ "$2" == "win32" ]; then
  echo "Building .zip for win32..."
  ARCH="win32"
  ARCHPATH="products/CLI-E4/win32/win32/x86_64"
  ADDS+=("adds/z3.exe" "adds/cvc5.exe" "adds/mathsat.exe" "adds/mpir.dll" "adds/mathsat.dll")
else
  echo "Wrong argument: ""$2"" -- use 'linux' or 'win32'"
  exit 1
fi


# set version 
VERSION=$(git rev-parse HEAD | cut -c1-8)
echo "Version is $VERSION"


TARGETDIR=U${TOOLNAME}-${ARCH}
CONFIGDIR="$TARGETDIR"/config
DATADIR="$TARGETDIR"/data
ZIPFILE=Ultimate${TOOLNAME}-${ARCH}.zip
SETTINGS=../../trunk/examples/settings/default/${LCTOOLNAME}/*${TOOLNAME}*

# check all toolchain arguments 
if [ -n "$3" -a ! "NONE" = "$3" ]; then
  TOOLCHAIN=../../trunk/examples/toolchains/${3}
else 
  echo "No reach toolchain specified, ommitting..."
  TOOLCHAIN=
fi

if [ ! -z "$4" -a ! "NONE" = "$4" ]; then
  TERMTOOLCHAIN=../../trunk/examples/toolchains/${4}
else
  echo "No termination toolchain specified, ommitting..."
  TERMTOOLCHAIN=
fi

if [ ! -z "$5" -a ! "NONE" = "$5" ]; then
  VALTOOLCHAIN=../../trunk/examples/toolchains/${5}
else 
  echo "No witness validation toolchain specified, ommitting..."
  VALTOOLCHAIN=
fi

if [ ! -z "$6" -a ! "NONE" = "$6" ]; then
  MEMDEREFMEMTRACKTOOLCHAIN=../../trunk/examples/toolchains/${6}
else 
  echo "No memory deref toolchain specified, ommitting..."
  MEMDEREFMEMTRACKTOOLCHAIN=
fi

if [ ! -z "$7" -a ! "NONE" = "$7" ]; then
  LTLTOOLCHAIN=../../trunk/examples/toolchains/${7}
else 
  echo "No LTL toolchain specified, ommitting..."
  LTLTOOLCHAIN=
fi

if [ ! -z "$8" -a ! "NONE" = "$8" ]; then
  TERMVALTOOLCHAIN=../../trunk/examples/toolchains/${8}
else 
  echo "No termination witness validation toolchain specified, ommitting..."
  TERMVALTOOLCHAIN=
fi


## removing files and dirs from previous deployments 
if [ -d "$TARGETDIR" ]; then
  echo "Removing old ""$TARGETDIR"
  rm -r "$TARGETDIR"
fi
if [ -f "${ZIPFILE}" ]; then
  echo "Removing old .zip file ""${ZIPFILE}"
  rm "${ZIPFILE}"
fi

## start copying files 
echo "Copying files"
mkdir "$TARGETDIR"
mkdir "$CONFIGDIR"
mkdir "$DATADIR"

exit_on_fail cp -a ../../trunk/source/BA_SiteRepository/target/${ARCHPATH}/* "$TARGETDIR"/
copy_if_non_empty "$TOOLCHAIN" "$CONFIGDIR"/"$TOOLNAME"Reach.xml
copy_if_non_empty "$TERMTOOLCHAIN" "$CONFIGDIR"/"$TOOLNAME"Termination.xml
copy_if_non_empty "$VALTOOLCHAIN" "$CONFIGDIR"/"$TOOLNAME"ReachWitnessValidation.xml
copy_if_non_empty "$MEMDEREFMEMTRACKTOOLCHAIN" "$CONFIGDIR"/"$TOOLNAME"MemDerefMemtrack.xml
copy_if_non_empty "$LTLTOOLCHAIN" "$CONFIGDIR"/"$TOOLNAME"LTL.xml
copy_if_non_empty "$TERMVALTOOLCHAIN" "$CONFIGDIR"/"$TOOLNAME"TerminationWitnessValidation.xml
exit_on_fail cp ${SETTINGS} "$CONFIGDIR"/.

## copy all adds to target dir 
for add in "${ADDS[@]}" ; do 
  if ! readlink -fe $add > /dev/null ; then
    echo "$add does not exist, aborting..."
    exit 1
  fi
  exit_on_fail cp $add "$TARGETDIR"/
done 


echo "Modifying Ultimate.py with version and toolname"
## replacing version value in Ultimate.py
exit_on_fail sed "s/^version =.*$/version = \'$VERSION\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

## replacing toolname value in Ultimate.py
exit_on_fail sed "s/toolname =.*/toolname = \'$TOOLNAME\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

## creating new zipfile 
echo "Creating .zip"
exit_on_fail zip -q "${ZIPFILE}" -r "$TARGETDIR"/*

