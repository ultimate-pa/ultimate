#!/bin/bash 
# Author: Daniel Dietsch
# Script to scan through a set of Ultimate logs and extract an overview 


## GLOBALS 
valid=0
overapprox=0
overapprox_but_bit_success=0
result_types=()

declare -A exceptions
declare -A timeouts
declare -A safe
declare -A unsafe
declare -A unknown
no_result=()

known_exceptions=( 
"we do not support pthread"
"unable to decide satisfiability of path constraint"
"UnsupportedSyntaxResult"
"TypeErrorResult"
"SyntaxErrorResult"
"overapproximation of large string literal"
"TerminationAnalysisResult: Unable to decide termination"
"An exception occured during the execution of Ultimate: The toolchain threw an exception"
"overapproximation of shiftRight"
"overapproximation of overflow check for bitwise shift operation"
"overapproximation of bitwiseAnd"
"overapproximation of shiftLeft"
"overapproximation of memtrack"
"There is insufficient memory for the Java Runtime Environment to continue"
"ExceptionOrErrorResult"
)

known_timeouts=(
"Cannot interrupt operation gracefully because timeout expired. Forcing shutdown"
"Toolchain execution was canceled (user or tool) before executing"
)

known_safe=(
"AllSpecificationsHoldResult"
"TerminationAnalysisResult: Termination proven"
)

known_unsafe=(
"CounterExampleResult"
"NonterminatingLassoResult"
)



function printUsage(){
    exit 1
}

function saveUltimateCall(){
    local -n array="$1"
    local line="$2"
    calls=`grep -oP "java.*-jar.*$" "$line"`
    array+=("$calls")
}

function scanLog(){
    local -n file_content="$1"
    local line="$2"
    local length=${#file_content}

    if [[ "$length" == "0" ]]; then 
        if grep -q 'No suitable settings file found' "$line"; then
            exceptions["No suitable settings file found"]=$((exceptions["No suitable settings file found"]+1))
            return
        fi
        timeouts["Unexpected end"]=$((timeouts["Unexpected end"]+1))
        return
    fi 
    
    length=$((length-4))
    if [[ "${file_content:$length:4}" == "...." ]]; then
        timeouts["Unexpected end"]=$((timeouts["Unexpected end"]+1))
        return
    fi

    if echo "$file_content" | grep -q 'ExceptionOrErrorResult'; then
        exc=`echo "$file_content" | grep -A1 'ExceptionOrErrorResult' | grep -v 'ExceptionOrErrorResult'`
        if [ ! -n "$exc" ]; then 
            exc=`echo "$file_content" | grep 'ExceptionOrErrorResult'`
        fi
        exc=`echo "$exc" | sed 's/\\$//g'`
        exceptions["$exc"]=$((exceptions["$exc"]+1))
        saveUltimateCall no_result "$line"
        return
    fi
    for i in "${known_exceptions[@]}"; do 
        if echo "$file_content" | grep -q "$i"; then
            exceptions["$i"]=$((exceptions["$i"]+1))
            saveUltimateCall no_result "$line"
            return
        fi
    done

    if echo "$file_content" | grep -qP 'Timeout.*Result'; then
        exc=`echo "$file_content" | grep -A1 -P 'Timeout.*Result' | grep -vP 'Timeout.*Result' | cut -c 1-120`
        timeouts["$exc"]=$((timeouts["$exc"]+1))
        saveUltimateCall no_result "$line"
        return
    fi
    for i in "${known_timeouts[@]}"; do 
        if echo "$file_content" | grep -q "$i"; then
            timeouts["$i"]=$((timeouts["$i"]+1))
            saveUltimateCall no_result "$line"
            return
        fi
    done

    for i in "${known_unsafe[@]}"; do 
        if echo "$file_content" | grep -q "$i"; then
            unsafe["$i"]=$((unsafe["$i"]+1))
            valid=$((valid+1))
            [ $bit_precise == 1 ] && ((overapprox_but_bit_success++))
            return
        fi
    done
   
    for i in "${known_safe[@]}"; do 
        if echo "$file_content" | grep -q "$i"; then
            safe["$i"]=$((safe["$i"]+1))
            valid=$((valid+1))
            [ $bit_precise == 1 ] && ((overapprox_but_bit_success++))
            return
        fi
    done
    
    # might help to get the results 
    #grep -oP "\s+\- \w*Result\w*"
    
    unknown["$line"]=$((unknown["$line"]+1))
    saveUltimateCall no_result "$line"
    return
}

sep_line_bitprecise="Retrying with bit-precise analysis"
sep_line_ultoutput="Real Ultimate output"
sep_line_ultversion="This is Ultimate"

function scanLogs(){
    local dir="$1"
    local iname="$2"
    local log_files=($(find "$dir" -type f -iname "$iname"))
    count=0
    local content=()
    
    echo "Processing ${#log_files[@]} files..."
    
    for log_file in ${log_files[@]}; do
        printf .
        grep -q "$sep_line_ultversion" "$log_file"
        if [ ! $? -eq 0 ]; then 
            echo "Not Ultimate log: $log_file"
            continue
        fi
        count=$((count+1))
        bit_precise=0
        grep -q "$sep_line_bitprecise" "$log_file"
        if [ $? -eq 0 ]; then 
            # is a Ultimate.py logfile, is after bit-precise 
            bit_precise=1
            overapprox=$((overapprox+1))
            content=`sed -e "1,/### Bit-precise run ###/d" "$log_file"`
        else
            grep -q "${sep_line_ultoutput}" "$log_file"
            if [ $? -eq 0 ]; then 
                # is a Ultimate.py logfile, is non-bitprecise output 
                content=`sed -e "1,/$sep_line_ultoutput/d" "$log_file"`
            else
                # is not Ultimate.py logfile, assume normal Ultimate log
                content=`cat $log_file`
            fi
        fi 
        
        scanLog content $log_file
    done 
    printf "\n"
    
}

function printArrayCount(){
    local -n array="$1"
    local message="$2"
    
    local tot=0
    for i in ${array[@]}; do
        let tot+=$i
    done
    echo "$tot $message"
}

function printArrayContent(){
    local -n array="$1"

    for i in "${!array[@]}"; do 
        echo "${array[$i]} : $i" 
    done | sort -rn     
}

function printResults(){
    echo "$valid of $count valid ($overapprox tried bit-precise analysis, $overapprox_but_bit_success succeeded)"
    printArrayCount safe "safe"
    printArrayCount unsafe "unsafe"
    echo ""
    printArrayCount exceptions "exceptions"
    printArrayContent exceptions
    echo ""
    printArrayCount timeouts "timeouts"
    printArrayContent timeouts
    echo ""
    printArrayCount unknown "unknowns"
    printArrayContent unknown
    echo ""
    echo "${#no_result[@]} no safe/unsafe result"
    for i in "${no_result[@]}"; do 
        echo "$i" 
    done 
}

function getUnhandledResults(){
    result_types=($(grep -hroP "\s+\- \w*Result\w*" "$1" | grep -oP "\w+" | sort | uniq))
    me=`dirname "$(readlink -f "$0")"`/`basename "$0"`
    
    for i in "${result_types}"; do 
        grep -q "$i" "$me"
        if [ ! $? -eq 0 ]; then 
            echo "Unhandled result type $i in logfiles"
        fi
    done 
}

getUnhandledResults "$1"
scanLogs "$1" "$2"
printResults


