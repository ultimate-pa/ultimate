#!/bin/bash
# script that prepares a .req file with the reasons for vacuity for a known vacuous requirement
# start it from the initial dump directory

orig_req_file="${1}"
ultimate_log="${2}"

bosch_repo="/storage/repos/bosch"
ultimate_repo="/storage/repos/ultimate"
explode="${bosch_repo}/explode_script.py"
ultimate_dir="${ultimate_repo}/releaseScripts/default/UAutomizer-linux"
tmp_dump_dir="dump-ss"
dump_dir="dump"


function check_params(){
    if [[ $PWD != *"$dump_dir" ]]; then
        echo "Not in directory $dump_dir"
        exit 1;
    fi
}

function parse_results(){
    mapfile -t results < <( grep -oP ' - .*Result.*' "$ultimate_log" | grep 'is vacuous' | grep -oP 'Requirement .* is' | cut -d ' ' -f 2 )
}

function print_results(){
    if [ ${#results[@]} -eq 0 ]; then
        echo "No vacuous requirements remaining! This is unexpected. Check $reduced_req_file and $ultimate_log"
        return 1
    else
        echo "${#results[@]} requirements still vacuous: ${results[@]}"
		return 0
    fi
}


function get_involved_reqs(){
    local reason_file="$req_id.vac"
    local tmp_file="$req_id.tmp"
    local regexpr=""

    if readlink -e "$tmp_file" > /dev/null ; then
        echo "$tmp_file still exists"
        exit 1
    fi

    for smt_file in $smt_file_pref
    do
        echo "Considering $smt_file"
        tmp_smt_file="${smt_file}.lbe"
        eval "$explode -i $smt_file -o $tmp_smt_file"
        if ! readlink -e "$tmp_smt_file" > /dev/null ; then
            echo "$explode -i $smt_file -o $tmp_smt_file did not produce the expected output, something is wrong"
            echo "The current folder is $PWD"
            exit 1
        fi
        sed -i 's/(get-interpolants.*/(get-unsat-core)/g' "$tmp_smt_file"
        sed -i '/\:interpolant-check-mode/d' "$tmp_smt_file"
        sed -i '/\:proof-transformation/d' "$tmp_smt_file"
        sed -i '/\:array-interpolation/d' "$tmp_smt_file"
        # You can check if z3 complains about something in the file
        #../z3 "$tmp_smt_file"
        for i in `"$ultimate_dir/z3" "$tmp_smt_file" | grep -A 1 -P ^unsat$ | tail -n +2 | sed 's/(//g' | sed 's/)//g'`; do grep "$i" "$tmp_smt_file"; done | grep -oP 'SysRS_\w+_\d+_\d+' | sort | uniq >> "$tmp_file"
        rm "$tmp_smt_file"
    done

    sort "$tmp_file" | uniq > "$reason_file"
    rm "$tmp_file"

    if ! grep -q "$req_id" "$reason_file" ; then
        echo "TODO: if the tmp_file does not contain the req_id in the unsat core, we need to remove reasons for infeasibility and try again"
        return 1
    fi

    echo "Found `wc -l $reason_file | cut -d " " -f 1` involved reqs"
    tr '[:space:]' ' ' < "$reason_file"
    echo ""

    for i in `cat $reason_file` ; do regexpr+="\|$i.*$"; done
    rm "$reason_file"
    sed "/CONST.*$\|Input.*$""$regexpr/!d" "$orig_req_file" > "$reduced_req_file"
    return 0
}

function run_ultimate_ss(){
    rm -r "$tmp_dump_dir"
    mkdir "$tmp_dump_dir"
    ultimate_log=`readlink -f "${tmp_dump_dir}/ultimate.log"`
    echo "Running Ultimate"
    java -Dosgi.configuration.area=config/ \
    -Xmx10G \
    -jar plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar \
    -tc "${ultimate_repo}/trunk/examples/toolchains/ReqCheck.xml" \
    -s "${bosch_repo}/reqanalyzer-nonlin.epf" \
    -i "${dump_dir}/$reduced_req_file" \
    --pea2boogie.check.consistency false \
    --pea2boogie.check.rt-inconsistency false \
    --traceabstraction.dump.smt.script.to.file true \
    --traceabstraction.to.the.following.directory="${tmp_dump_dir}/" \
    > "$ultimate_log"
}

check_params
parse_results
initial_results="${results[@]}"
echo "Processing ${#results[@]} vacuous requirements"
for i in ${initial_results[@]}
do
    req_id="$i"
    reduced_req_file="$req_id.vac.req"
    echo "----"
    echo "Processing $req_id"
    smt_file_pref="*VAC*_"`echo "$req_id" | cut -d "_" -f 3-`"_*.smt2"

    if ! get_involved_reqs ; then
      continue
    fi

    pushd "$ultimate_dir" > /dev/null

    run_ultimate_ss
    parse_results
    if print_results ; then
      pushd "$tmp_dump_dir" > /dev/null
      get_involved_reqs
      echo "Writing $reduced_req_file"
      cp "$reduced_req_file" "../${dump_dir}/"
      cp "$reduced_req_file" "../"
      popd > /dev/null
    fi

    # If you are unsure you can re-run ultimate a third time ....
    #run_ultimate_ss
    #parse_results
    #print_results
    #
    #pushd "$tmp_dump_dir" > /dev/null
    #get_involved_reqs
    #cp "$reduced_req_file" "../"
    #popd > /dev/null

    popd > /dev/null

    echo "Finished $req_id"
    echo ""
done
