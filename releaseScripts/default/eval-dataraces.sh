#!/bin/bash

###############################################################################
#
# EVAL-DATARACES.SH
#
# Evaluates data-race detection with all tools that support concurrency.
#
###############################################################################

set -e

if [ "$#" -ne 0 ]
then
  echo "
Evaluates data-race detection with all tools that support concurrency.
(Assumes that run-benchexec.sh is on the PATH.)

USAGE: ./eval-dataraces.sh

"
  exit 1
fi

DIR=$(realpath $(dirname "$0"))
cd "$DIR"

###############################################################################

get_tool_path () {
  echo "$DIR/U$1-linux"
}

get_datarace_xml () {
  echo "$DIR/benchexec/dataraces-${1,,}.xml"
}

get_results_dir () {
  echo "$DIR/results-tmp/results-$1"
}

check_no_results () {
  resultsdir="$(get_tool_path $1)/results"
  if [ -d "$resultsdir" ]
  then
    echo "ERROR: Directory $resultsdir already exists."
    exit 1
  fi
}

eval_dataraces () {
  # run evaluation
  cd $(get_tool_path $1)
  run-benchexec.sh --numOfThreads=14 "$(get_datarace_xml $1)"
  mv results "$(get_results_dir $1)"

  # extract overview
  cd "$(get_results_dir $1)"
  python3 "$DIR/../benchmark-processing/get-benchexec-overview.py" -i . > overview.txt

  # reset directory
  cd "$DIR"
}

###############################################################################

VERIFIERS=(Automizer GemCutter Taipan)

for TOOL in "${VERIFIERS[@]}"
do
   check_no_results "$TOOL"
done

./makeFresh.sh
mkdir results-tmp

for TOOL in "${VERIFIERS[@]}"
do
   eval_dataraces "$TOOL"
done

echo
echo "Packaging results in archive..."
tar cJf results-dataraces.tar.xz results-tmp/

echo "======================================================"
echo
echo "results stored in $(realpath ./results-tmp)"
echo

