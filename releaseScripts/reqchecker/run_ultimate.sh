#!/bin/bash
# script that runs Ultimate on a .req file with all the matching settings, generating a .log in the right place
# Note that you can change the memory limit by altering the actual Ultimate call at the end (the -Xmx setting) 

# folder where .req files reside
req_location="./reqs/"
# folder of automizer, e.g. result of makeFresh.sh
automizer_location="./UAutomizer-linux"
# toolchain for ReqChecker
toolchain_location="ReqCheck.xml"
# settings for ReqChecker
settings_location="reqanalyzer-nonlin.epf"
reqchecker_timeout=900

function prompt {
    read -p "${1} [y/N]" -n 1 -r
    echo ""
    if [[ $REPLY =~ ^[Yy]$ ]] ; then
        return 0
    fi
    return 1
}

if (( $# == 0 )); then
    echo "Specify at least one file"
    exit 1
elif (( $# == 1 )); then
    file=`readlink -f "$1"`
    log="$req_location"`basename $file`".log"
else
    length=$(($#-1))
    file="${@:1:$length}"
    log="$req_location${@: -1}"
fi

for i in "$automizer_location" "$req_location" ; do
  if [ ! -d "$i" ]; then
      echo "$i does not exist"
      exit 1
  fi
done

for i in "$toolchain_location" "$settings_location" ; do
  if [ ! -f "$i" ]; then
      echo "$i does not exist"
      exit 1
  fi
done

pushd "$automizer_location" > /dev/null

if ! readlink -e "$PWD/plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar" > /dev/null ; then
    echo "$PWD does not contain Ultimate binaries"
    exit 1
fi

if readlink -e "$PWD/dump" > /dev/null ; then
    echo "Found old dump directory $PWD/dump"
    if prompt "Should I delete the directory?" ; then
        rm -r "$PWD/dump"
    else
        exit 1
    fi
fi


if [[ $log != *".log" ]]; then
    echo "Logfile $log does not end in .log"
    exit 1;
fi

if readlink -e "$log" > /dev/null ; then
    echo "Logfile $log already exists"
    if prompt "Overwrite?" ; then
        rm "$log"
    else
        exit 1
    fi
fi

echo "Analyzing $file"
echo "Using log file $log"
mkdir dump

#-XX:+HeapDumpOnOutOfMemoryError \
# -agentlib:hprof=cpu=samples,interval=20,depth=6,doe=y,heap=sites
# will dump to java.hprof(.txt)
java \
-Dosgi.configuration.area=config/ \
-Xmx100G \
-Xss4m \
-jar plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar \
-tc "$toolchain_location" \
-s "$settings_location" \
-i $file \
--core.print.statistic.results false \
--traceabstraction.dump.smt.script.to.file true \
--traceabstraction.to.the.following.directory=dump/ \
--traceabstraction.limit.analysis.time $reqchecker_timeout \
--pea2boogie.always.use.all.invariants.during.rt-inconsistency.checks true \
--pea2boogie.check.vacuity true \
--pea2boogie.check.consistency true \
--pea2boogie.check.rt-inconsistency true \
--pea2boogie.report.trivial.rt-consistency false \
--pea2boogie.rt-inconsistency.range 2 \
> "$log"

echo "Used log file $log"

popd > /dev/null
exit 0

