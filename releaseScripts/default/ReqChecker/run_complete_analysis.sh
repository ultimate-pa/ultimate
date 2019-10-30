#!/bin/bash
# script that runs all the various requirement analysis scripts and moves files around in the matching directories

# The requirement file is an argument passed to this script.
req_file="$1"

### Default settings
# This is the path to the repository, which contains the requirements-folder
req_repo_folder="/repos/hanfor/example_input"
# This is the path to the requirements-folder
req_folder="/repos/hanfor/example_input"
# The amount of requirements which are checked together for RT-inconsistency.
# Careful with this parameter, it will blow up the amount of checks really fast.
rt_inconsistency_range=2
# The time how long a singles assertion is checked.
timeout_per_assertion=900

# Don't touch this, unless you know what you are doing.
automizer_folder="."
# Path to the vacuity extractor script.
vac_extractor="./extract_vac_reasons.sh"
# Path to Ultimate Automizer (remember those binaries we created earlier? that's what you want!).
reqcheck_toolchain="./config/ReqCheck.xml"
reqcheck_settings="./config/ReqCheck-nonlin.epf"
testgen_toolchain="./config/ReqToTest.xml"
testgen_settings="./config/ReqCheck-ReqToTest.epf"

### Functions
function prompt {
  read -p "${1} [y/N]" -n 1 -r
  echo ""
  if [[ $REPLY =~ ^[Yy]$ ]] ; then
      return 0
  fi
  return 1
}

function test_if_cmd_is_available {
  local cmd_path=`command -v "$@"`
  [ $? -eq 0 ] || { echo >&2 "I require $@ but it's not installed. Aborting."; exit 1; }
  if ! [[ -f "$cmd_path" && -x $(realpath "$cmd_path") ]]; then
    echo >&2 "I require $@ but it's not executable. Aborting."; exit 1;
  fi
}

function exitOnFail {
  "$@"
  local status=$?
  if [ $status -ne 0 ]; then
              echo "$@ failed with $1"
              exit $status
  fi
  return $status
}

function run_reqcheck {
  pushd "$automizer_folder" > /dev/null

  local dump_folder="$PWD""/dump-"`basename $req_file`

  if ! readlink -e "$PWD/plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar" > /dev/null ; then
    echo "$PWD does not contain Ultimate binaries"
    exit 1
  fi

  if readlink -e "$dump_folder" > /dev/null ; then
    echo "Found old dump directory $dump_folder"
    if prompt "Should I delete the directory?" ; then
      rm -r "$dump_folder"
    else
      exit 1
    fi
  fi

  if readlink -e "$reqcheck_log" > /dev/null ; then
    echo "Logfile $reqcheck_log already exists"
    if prompt "Overwrite?" ; then
        rm "$reqcheck_log"
    else
        exit 1
    fi
  fi

  echo "Analyzing $req_file"
  echo "Using log file $reqcheck_log"
  mkdir "$dump_folder"

  java \
  -Dosgi.configuration.area=config/ \
  -Xmx100G \
  -Xss4m \
  -jar plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar \
  -tc "$reqcheck_toolchain" \
  -s "$reqcheck_settings" \
  -i "$req_file" \
  --core.print.statistic.results false \
  --traceabstraction.dump.smt.script.to.file true \
  --traceabstraction.to.the.following.directory="$dump_folder" \
  --traceabstraction.limit.analysis.time $timeout_per_assertion \
  --pea2boogie.always.use.all.invariants.during.rt-inconsistency.checks true \
  --pea2boogie.check.vacuity true \
  --pea2boogie.check.consistency true \
  --pea2boogie.check.rt-inconsistency true \
  --pea2boogie.report.trivial.rt-consistency false \
  --pea2boogie.rt-inconsistency.range $rt_inconsistency_range \
  > "$reqcheck_log"

  popd > /dev/null


  ### Postprocess results with vacuity extractor
  if [ ! -f "$reqcheck_log" ]; then
    echo "File $reqcheck_log was not created; aborting."
    exit 1
  fi

  echo "Extracting results to $reqcheck_relevant_log"
  grep "  -" "$reqcheck_log" | grep -v "StatisticsResult" | grep -v "ReqCheckSuccessResult" \
  > "$reqcheck_relevant_log"

  if grep -q "vacuous" "$reqcheck_relevant_log" ; then
    echo "Analyzing reasons for vacuity"
    pushd "$dump_folder" > /dev/null
    exitOnFail ${vac_extractor} "$req_file" "$reqcheck_log" "$req_repo_folder" "$ultimate_repo_folder"
    mv *.vac.req "$log_folder""/"
    popd > /dev/null
  else
    echo "No vacuities found"
  fi
}

function run_testgen {
  echo "Using log file $testgen_log"

  pushd "${automizer_folder}" > /dev/null
  if ! readlink -e "$PWD/plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar" > /dev/null ; then
    echo "$PWD does not contain Ultimate binaries"
    exit 1
  fi

  java \
  -Dosgi.configuration.area=config/ \
  -Xmx100G \
  -Xss4m \
  -jar plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar \
  -tc "$testgen_toolchain" \
  -s "$testgen_settings" \
  -i "$req_file" \
  --core.print.statistic.results false \
  --rcfgbuilder.simplify.code.blocks false \
  --rcfgbuilder.size.of.a.code.block LoopFreeBlock \
  --traceabstraction.limit.analysis.time $timeout_per_assertion \
  --rcfgbuilder.add.additional.assume.for.each.assert false \
  > "$testgen_log"

  sed -ne '/--- Results ---/,$p' "$testgen_log" > "$testgen_relevant_log"

  popd > /dev/null
}

### Check parameters
for i in "$automizer_folder" "$req_folder" ; do
  if [ ! -d "$i" ]; then
    echo "Folder $i does not exist"
    exit 1
  fi
done

for i in "$req_file" "$reqcheck_toolchain" "$reqcheck_settings" "$testgen_toolchain" "$testgen_settings" ; do
  if [ ! -f "$i" ]; then
    echo "File $i does not exist"
    exit 1
  fi
done

test_if_cmd_is_available ${vac_extractor}

req_file=`readlink -f "$req_file"`
reqcheck_log="$req_folder""/"`basename $req_file`".log"
testgen_log="$req_folder""/"`basename $req_file`".testgen.log"

req_file_name=$(basename -- "$req_file")
req_file_name="${req_file_name%.*}"

log_folder="$req_folder""/logs/""$req_file_name"
reqcheck_relevant_log="$log_folder""/""$req_file_name"".req.relevant.log"
testgen_relevant_log="$log_folder""/""$req_file_name"".req.testgen.log"


### Prepare folders
if [ ! -d "$log_folder" ]; then
  if prompt "$log_folder does not exist, should I create it?" ; then
    mkdir -p "$log_folder"
  else
    exit 2
  fi
fi


### Start running actual tools
echo "Running ReqChecker"
exitOnFail run_reqcheck

echo "Running TestGen"
exitOnFail run_testgen


### Print result summary
cat<<EOF
Results for $1
Test-cases:            $testgen_relevant_log
ReqChecker results:    $reqcheck_relevant_log
Reasons for vacuity:   `grep -q "vacuous" "$reqcheck_relevant_log" && ls ${log_folder}/*.vac.req`
Full ReqCheck logfile  $reqcheck_log
Full TestGen logfile   $testgen_log
EOF

exit 0
