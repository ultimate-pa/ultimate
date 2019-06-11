#!/bin/bash
# script that runs all the various requirement analysis scripts and the testgen script and moves files around in the matching directories


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

# git repository where you store your reports and reuslts
repo_location="./repo"
# directory where the .req files lie, usually relative to repository 
req_location="${repo_location}/reqs"
# location of UltimateAutomizer (i.e., result of makeFresh.sh)
automizer_location="/storage/repos/ultimate/releaseScripts/default/UAutomizer-linux"
# location of vacuity extraction script, usually  relative to repository 
vac_extractor="${repo_location}/extract_vac_reasons.sh"
req_file="$1"
if [ ! -f "$req_file" ]; then
    echo "File $req_file does not exist!"
    exit 1
fi

test_if_cmd_is_available run_ultimate.sh
test_if_cmd_is_available ${vac_extractor}
test_if_cmd_is_available ${automizer_location}/run-ultimate.sh

req_file=`readlink -f "$req_file"`
log_file="$req_location""/"`basename $req_file`".log"

req_file_name=$(basename -- "$req_file")
req_file_name="${req_file_name%.*}"

req_log_folder="$req_location""/logs/""$req_file_name"
req_relevant_log="$req_log_folder""/""$req_file_name"".req.relevant.log"
req_testgen_log="$req_log_folder""/""$req_file_name"".req.testgen.log"

if [ ! -d "$req_log_folder" ]; then
  if prompt "$req_log_folder does not exist, should I create it?" ; then 
    mkdir -p "$req_log_folder"
  else
    exit 2
  fi
fi

echo "Running ReqChecker"
exitOnFail run_ultimate.sh "$req_file"

if [ ! -f "$log_file" ]; then
    echo "File $log_file was not created; aborting."
    exit 1
fi

echo "Extracting results to $req_relevant_log"
grep "  -" "$log_file" | grep -v "StatisticsResult" | grep -v non-vacuous | grep -v "are rt-consistent" \
> "$req_relevant_log"

if grep -q "vacuous" "$req_relevant_log" ; then 
  echo "Analyzing reasons for vacuity"
  pushd "${automizer_location}/dump" > /dev/null
  exitOnFail ${vac_extractor} "$req_file" "$log_file"
  mv *.vac.req "$req_log_folder""/"
  popd > /dev/null
else 
  echo "No vacuities found"
fi

echo "Generating test cases to $req_testgen_log"
pushd "${automizer_location}" > /dev/null
./run-ultimate.sh \
-tc ../../../trunk/examples/toolchains/ReqToTest.xml \
-s ../../../trunk/examples/settings/ReqToTest.epf \
-i "$req_file" \
--rcfgbuilder.simplify.code.blocks false \
--rcfgbuilder.size.of.a.code.block LoopFreeBlock \
--traceabstraction.limit.analysis.time 900 \
--rcfgbuilder.add.additional.assume.for.each.assert false \
> testgen-ultimate.log

sed -ne '/--- Results ---/,$p' testgen-ultimate.log > "$req_testgen_log"

popd > /dev/null

cat<<EOF
Results for $1 
Test-cases:           $req_testgen_log
ReqChecker results:   $req_relevant_log
Reasons for vacuity:  `grep -q "vacuous" "$req_relevant_log" && ls ${req_log_folder}/*.vac.req`
EOF

exit 0

