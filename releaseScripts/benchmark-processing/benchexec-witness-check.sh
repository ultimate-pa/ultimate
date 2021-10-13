#!/bin/bash
# 
# Script for one of the benchmark containers on mariachi that runs 
# - benchexec in container mode on a SV-COMP benchmark definition (xml) for one of the ultimate tools 
# - followed by some witness validators 
# - followed by post-processing scripts (merge xmls for scores, compute tables, generate ultimate-specific overview files, move logs and results to central location)
#
# Note that there may be a lot of assumptions about directory layout, so you are encouraged to test it on a very small sample set (that you probably have to build by yourself)

# Rough outline 
# - Run Ultimate on benchmark def 
# - Generate results with post processing for that
# - Modify SV-COMP benchmark definitions for witness validators s.t. paths match 
# - Run witness validators 
# - Run merge scripts from SV-COMP
# - Run table generator 
# - Pack everything and move it to target webserver 

shopt -s extglob

BENCH_DEF_FOLDER="/storage/repos/ultimate/releaseScripts/default/benchexec"
DIVISION_PARAMS="--numOfThreads=14 -r SV-COMP21_unreach-call -t ConcurrencySafety-Main"
UAUTOMIZER_FOLDER="/storage/repos/ultimate/releaseScripts/default/UAutomizer-linux"
VERIFIER_RESULTS_FOLDER="results-verifier"
VALIDATOR_RESULTS_FOLDER="results-validator"
MERGED_RESULTS_FOLDER="results-merged"

function join_by() {
  local d=${1-} f=${2-}
  if shift 2; then
    printf %s "$f" "${@/#/$d}" 
  fi
}

function git_hash(){
  git rev-parse --short HEAD
}

function benchexec(){
  /storage/repos/benchexec/bin/benchexec --no-compress-results --maxLogfileSize=-1 --hidden-dir /home --hidden-dir /run --hidden-dir /tmp $@
}

function replace_paths_in_xml(){
  sed "s|../../results-verified/LOGDIR/\${rundefinition_name}.\${taskdef_name}/witness.graphml|${UAUTOMIZER_FOLDER}/${VERIFIER_RESULTS_FOLDER}/${3}/\${rundefinition_name}/\${taskdef_name}/witness.graphml|g" "$1" | sed "s|../results-verified/LOGDIR/\${rundefinition_name}.\${taskdef_name}/witness.graphml|${UAUTOMIZER_FOLDER}/${VERIFIER_RESULTS_FOLDER}/${3}/\${rundefinition_name}/\${taskdef_name}/witness.graphml|g" > "$2"
}

function get_files_folder_name(){
  basename $(readlink -f "${UAUTOMIZER_FOLDER}/${VERIFIER_RESULTS_FOLDER}/*.files")
}

function prepare_validator_def_file(){
  witness_files=$(get_files_folder_name)
  if [ -z $witness_files ] ; then
    echo "Could not find witness file directory, aborting..."
    exit 1
  fi
  new_name="${1}.modified.xml"
  replace_paths_in_xml "$1" "${new_name}" "$witness_files"
  echo "${new_name}"
}

function benchexec_validator(){
  new_def=$(prepare_validator_def_file "$2")
  benchexec -o "${VALIDATOR_RESULTS_FOLDER}" --tool-directory "$1" "${new_def}" ${DIVISION_PARAMS}
  rm "${new_def}"
}

function move_results_create_overview(){
  if [ -d "$MERGED_RESULTS_FOLDER" ] ; then
    rm -r "$MERGED_RESULTS_FOLDER"
  fi
  mkdir "$MERGED_RESULTS_FOLDER"
  for f in "${VERIFIER_RESULTS_FOLDER}"/*xml ; do 
    parts=(${f//./ })
    suffix=$(join_by '.' ${parts[@]:3})
    PYTHONPATH=$PYTHONPATH:/storage/repos/benchexec /storage/repos/benchexec/contrib/mergeBenchmarkSets.py -o "${MERGED_RESULTS_FOLDER}" "${f}" "${VALIDATOR_RESULTS_FOLDER}/"*"${suffix}"
  done
  find "${MERGED_RESULTS_FOLDER}"/ -mindepth 2 -type f -exec mv {} "${MERGED_RESULTS_FOLDER}" \;
  find "${MERGED_RESULTS_FOLDER}"/ -mindepth 1 -type d -delete
  cp -r "${VERIFIER_RESULTS_FOLDER}"/* "${MERGED_RESULTS_FOLDER}"/
  for f in "${MERGED_RESULTS_FOLDER}"/*xml ; do 
    rm "$f"
  done
  bunzip2 "${MERGED_RESULTS_FOLDER}"/*.bz2

  # compute overview only for verifier results
  source move-benchexec-results "$(readlink -f "${MERGED_RESULTS_FOLDER}")" "svcomp-automizer"
  get_target_dir_name
  compute_overview

  # add validator results 
  cp -r "${VALIDATOR_RESULTS_FOLDER}"/* "${MERGED_RESULTS_FOLDER}"/

  # collect file names in a particular order (s.t. the verifiers are the first arguments)
  xml_files=""
  for f in "${MERGED_RESULTS_FOLDER}"/*merged.xml ; do
    xml_files="$xml_files ${f##*/}"
  done
  for f in "${MERGED_RESULTS_FOLDER}"/!(*merged).xml ; do
    xml_files="$xml_files ${f##*/}"
  done

  # move result to struebli
  move_result_dir
  remote_ssh "bash -c \"cd ${tag_dir}/${target_dir_name} ; /storage/repos/benchexec/bin/table-generator ${xml_files}\""
  echo "Results available at https://${remote_host}/logs/$(basename ${tag_dir})/${target_dir_name}"
}

# benchexec -o "${VERIFIER_RESULTS_FOLDER}/" --tool-directory "${UAUTOMIZER_FOLDER}" "${BENCH_DEF_FOLDER}/uautomizer-local.xml" ${DIVISION_PARAMS}
# benchexec_validator "/storage/repos/cpachecker" "${BENCH_DEF_FOLDER}/cpa-seq-validate-violation-witnesses.xml"
# benchexec_validator "/storage/repos/sv-witnesses/lint" "${BENCH_DEF_FOLDER}/witnesslint-validate-witnesses.xml"

# these are setup but do not support concurrency
#benchexec_validator "/storage/repos/cpachecker" "${BENCH_DEF_FOLDER}/cpa-seq-validate-correctness-witnesses.xml"
#benchexec_validator "${UAUTOMIZER_FOLDER}" "${BENCH_DEF_FOLDER}/uautomizer-validate-correctness-witnesses.xml"
#benchexec_validator "${UAUTOMIZER_FOLDER}" "${BENCH_DEF_FOLDER}/uautomizer-validate-violation-witnesses.xml"

# these may be interesting but still need setting up 
# ../benchexec/fshell-witness2test-validate-violation-witnesses.xml
# ../benchexec/nitwit-validate-violation-witnesses.xml
# ../benchexec/veriabs-validate-correctness-witnesses.xml
# ../benchexec/veriabs-validate-violation-witnesses.xml

move_results_create_overview
