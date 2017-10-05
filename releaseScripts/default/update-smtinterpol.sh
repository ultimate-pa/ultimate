#!/bin/bash 
# Tries to update SMTInterpol in Ultimate to the newest version 
# Execute it from a folder where SMTInterpol and Ultimate are both subfolders 

exitOnFail() {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with exit code $status"
		exit $status
    fi
    return $status
}

dir_smtinterpol="/mnt/crypto-storage/firefox/repo/smtinterpol"
dir_ultimate="/mnt/crypto-storage/firefox/repo/ultimate"
diff_file="smtinterpol.diff"

if [ ! -d "$dir_smtinterpol" ]; then 
	echo "Could not find directory $dir_smtinterpol"
	exit 1
fi 

if [ ! -d "$dir_ultimate" ]; then 
	echo "Could not find directory $dir_ultimate"
	exit 1
fi 

echo "Updating $dir_smtinterpol..."
pushd "$dir_smtinterpol" > /dev/null 
exitOnFail git fetch
exitOnFail git rebase
exitOnFail git clean -f -d 
echo "Building SMTInterpol..."
exitOnFail ant > /dev/null
smtinterpol_cur=`git describe --tags` 
popd > /dev/null

echo "Updating $dir_ultimate..."
pushd "$dir_ultimate" > /dev/null
exitOnFail git fetch 
exitOnFail git rebase
smtinterpol_ver=`grep version trunk/source/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.properties | cut -d'=' -f 2`
popd > /dev/null

echo "Normalizing versions..."
smtinterpol_hash=`echo $smtinterpol_cur | cut -d'-' -f 3`
ultimate_hash=`echo $smtinterpol_ver | cut -d'-' -f 3`
smtinterpol_prehash=`echo $smtinterpol_cur | cut -d'-' -f 1-2`
ultimate_prehash=`echo $smtinterpol_ver | cut -d'-' -f 1-2`
smtinterpol_curnorm="$smtinterpol_prehash""-""${smtinterpol_hash:0:8}"
smtinterpol_vernorm="$ultimate_prehash""-""${ultimate_hash:0:8}"

echo "SMTInterpol version is $smtinterpol_cur (normalized: $smtinterpol_curnorm)"
echo "Ultimate normalized is $smtinterpol_ver (normalized: $smtinterpol_vernorm)"

smtinterpol_cur="$smtinterpol_curnorm"
smtinterpol_ver="$smtinterpol_vernorm"

if [ "$smtinterpol_ver" = "$smtinterpol_cur" ]; then 
	echo "No update necessary, version is already the latest ($smtinterpol_cur)"
	exit 0
fi

echo "Latest SMTInterpol version is $smtinterpol_cur, in Ultimate is $smtinterpol_ver, updating..."
pushd "$dir_smtinterpol" > /dev/null 
echo "Creating diff..."
[ -e "$diff_file" ] && rm "$diff_file"
git diff "$smtinterpol_ver" -- SMTInterpol/src Library-SMTLIB/src Library-SMTLIBTest/src SMTInterpolTest/src \
':(exclude,glob)**util/datastructures' \
':(exclude,glob)**util/HashUtils.java' \
':(exclude,glob)**util/ScopeUtils.java' \
':(exclude,glob)**/build-parser.xml' \
> "$diff_file"
popd > /dev/null

pushd "$dir_ultimate" > /dev/null 
echo "Applying patch..."
## first check, if nothing can be applied, do not update version
if git apply --check --directory=trunk/source/ "$dir_smtinterpol/smtinterpol.diff"; then 
	git apply --directory=trunk/source/ "$dir_smtinterpol/smtinterpol.diff"
	echo "Updating version"
	cp "$dir_smtinterpol"/SMTInterpol/release/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.properties "$dir_ultimate"/trunk/source/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.properties
	git commit -a -m"Updated SMTInterpol to $smtinterpol_cur"
else
	echo "Problems applying the patch, please check manually"
fi

popd > /dev/null

echo "Remember to manually check the changes, check for added files, and push"

