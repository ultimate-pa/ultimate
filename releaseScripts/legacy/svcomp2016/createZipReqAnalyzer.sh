#!/bin/bash

function test {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
        echo "$@ failed with $1"
        exit $status
    fi
    return $status
}


if [ $# -eq 0 ]; then
    echo "No arguments supplied -- use 'linux' or 'win32' as argument"
	exit 1
fi
if [ "$1" == "linux" ]; then
    echo "Building .zip for linux..."
	ARCH="linux"
	ARCHPATH="products/ReqAnalyzer/linux/gtk/x86_64"
elif [ "$1" == "win32" ]; then
	echo "Building .zip for win32..."
	ARCH="win32"
	ARCHPATH="products/ReqAnalyzer/win32/win32/x86_64"
else
    echo "Wrong argument: ""$1"" -- use 'linux' or 'win32'"		
	exit 1
fi

# set version 
VERSION=`git rev-parse HEAD | cut -c1-8`
echo "Version is "$VERSION
TOOLNAME=ReqAnalyzer
TARGETDIR=Ultimate-${TOOLNAME}-${ARCH}
ZIPFILE=Ultimate-${TOOLNAME}-${ARCH}.zip
TOOLCHAIN=../../trunk/examples/toolchains/AutomizerBpl.xml
SETTINGS=../../trunk/examples/settings/reqanalyzer/reqanalyzer.epf*

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
test cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
test cp LICENSE* "$TARGETDIR"/
test cp ${SETTINGS} "$TARGETDIR"/.
test cp Ultimate.ini "$TARGETDIR"/
test cp README.req "$TARGETDIR"/README
if [ "$1" == "linux" ]; then
	echo -e "#!/bin/bash\n\nif [ \$# -ne 1 ]; then\n   echo \"Wrong number of parameters.\"\n   echo\n   echo \"Usage: ./run.sh <requirements-file>\"\n   exit 1\nfi\n\n./ReqAnalyzer --console \"./ReqAnalyzer.xml\" \"\$1\" --settings \"reqanalyzer.epf\"" > "${TARGETDIR}/run.sh"
	chmod +x "${TARGETDIR}/run.sh"
elif [ "$1" == "win32" ]; then
	echo -e "@echo off\nsetlocal enabledelayedexpansion\n\nset argCount=0\nfor %%x in (%*) do (\n   set /A argCount+=1\n)\n\nif not \"%argCount%\"==\"1\" (\n   echo \"Wrong number of parameters.\"\n   echo.\n   echo \"Usage: run.bat <requirements-file>\n   goto :eof\n)\n\neclipsec.exe --console \".\\ReqAnalyzer.xml\" \"%1\" --settings \"reqanalyzer.epf\"" > "${TARGETDIR}/run.bat"
fi

echo "Creating .zip"
## creating new zipfile 
test zip -q ${ZIPFILE} -r "$TARGETDIR"/*

