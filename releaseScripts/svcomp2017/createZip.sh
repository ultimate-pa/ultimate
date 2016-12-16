#!/bin/bash

# Build latest version of Z3 or copy binary from Monteverdi
# Get CVC4 here: http://cvc4.cs.nyu.edu/downloads/

function test {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
        echo "$@ failed with $1"
        exit $status
    fi
    return $status
}

if [ $# -le 2 ]; then
    echo "Not enough arguments supplied -- use arguments in the following order"
	echo "1. the toolname" 
	echo "2. 'linux' or 'win32' for the target platform"
	echo "3. (optional) the reach toolchain (e.g., 'AutomizerC_WitnessPrinter.xml')"
	echo "4. (optional) the termination toolchain or NONE"
	echo "5. (optional) the witness validation toolchain or NONE"
	echo "6. (optional) the memsafety deref and memtrack toolchain or NONE"
	exit 1
fi

TOOLNAME="$1"
if [ -z "$TOOLNAME" ]; then
	echo "First argument (toolname) cannot be empty"		
	exit 1
fi
LCTOOLNAME="$(echo $TOOLNAME | tr '[A-Z]' '[a-z]')"
echo "using $TOOLNAME ($LCTOOLNAME) as toolname"


if [ "$2" == "linux" ]; then
    echo "Building .zip for linux..."
	ARCH="linux"
	ARCHPATH="products/CLI-E4/linux/gtk/x86_64"
	Z3PATH="adds/z3"
	CVC4PATH="adds/cvc4"
elif [ "$2" == "win32" ]; then
	echo "Building .zip for win32..."
	ARCH="win32"
	ARCHPATH="products/CLI-E4/win32/win32/x86_64"
	Z3PATH="adds/z3.exe"
	CVC4PATH="adds/cvc4.exe"
else
    echo "Wrong argument: ""$2"" -- use 'linux' or 'win32'"		
	exit 1
fi


# set version 
VERSION=`git rev-parse HEAD | cut -c1-8`
echo "Version is "$VERSION
TARGETDIR=U${TOOLNAME}-${ARCH}
ZIPFILE=Ultimate${TOOLNAME}-${ARCH}.zip

if [ ! -z "$3" -a ! "NONE" = "$3" ]; then
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

SETTINGS=../../trunk/examples/settings/svcomp2017/${LCTOOLNAME}/*${TOOLNAME}*

if [ -d "$TARGETDIR" ]; then
	echo "Removing old ""$TARGETDIR"
	rm -r "$TARGETDIR"
fi
if [ -f "${ZIPFILE}" ]; then
    echo "Removing old .zip file ""${ZIPFILE}"
	rm "${ZIPFILE}"
fi

echo "Copying files"
mkdir "$TARGETDIR"
test cp -a ../../trunk/source/BA_SiteRepository/target/${ARCHPATH}/* "$TARGETDIR"/
if [ ! -z "$TOOLCHAIN" ]; then 
	test cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"Reach.xml
fi
if [ ! -z "$TERMTOOLCHAIN" ]; then  
	test cp "$TERMTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"Termination.xml
fi
if [ ! -z "$VALTOOLCHAIN" ]; then 
	test cp "$VALTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"WitnessValidation.xml
fi
if [ ! -z "$MEMDEREFMEMTRACKTOOLCHAIN" ]; then 
	test cp "$MEMDEREFMEMTRACKTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"MemDerefMemtrack.xml
fi

test cp adds/LICENSE* "$TARGETDIR"/
test cp ${SETTINGS} "$TARGETDIR"/.
test cp adds/Ultimate.py "$TARGETDIR"/
test cp adds/Ultimate.ini "$TARGETDIR"/
test cp adds/README "$TARGETDIR"/
test cp ${Z3PATH} "$TARGETDIR"/
test cp ${CVC4PATH} "$TARGETDIR"/

echo "Creating .zip"
## replacing version value in Ultimate.py
test sed "s/version =.*/version = \'$VERSION\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

## replacing toolname value in Ultimate.py
test sed "s/toolname =.*/toolname = \'$TOOLNAME\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

## creating new zipfile 
test zip -q ${ZIPFILE} -r "$TARGETDIR"/*

