#!/bin/bash
# Date: 17.5.2014
# Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
# 
# Determine the status (sat/unsat) for SMT scripts

examplesFolder=$1;
if [ ! -e "$examplesFolder" ]; then
    echo "Folder $examplesFolder does not exist"
fi

solvers[0]="z3"
solvers[1]="princess"
solvers[2]="cvc4"
solvers[3]="smtinterpol"
#solvers[0]="z3"
echo "Solvers: ${solvers[*]}"



for f in `find "$examplesFolder" -name "*.smt2"`;
do
result=
resultCounter=0
    for((i=0;i<${#solvers[@]};i++))
    do
        #echo Solver ${solvers[$i]}
        solver=${solvers[$i]}
        resultFile="$f".${solvers[i]}_results.txt
        if [ ! -e "$resultFile" ]; then
            # echo "File $resultFile does not exist"
            resultFileContent=""
        else 
            resultFileContent=`cat "$resultFile"`
            if [ "$resultFileContent" == "unknown" ]; then
                sleep 0
                # echo "unknown"
            elif [ "$resultFileContent" == "sat" ]; then
                # echo "sat"
                if [ ! $result ]; then
                    result="sat"
                    resultCounter="1"
                elif [ $result == "sat" ]; then
                    result="sat"
                    resultCounter=$[$resultCounter + 1]
                else 
                    # echo "$solver" disagrees on result
                    result="error"
                fi
            elif [ "$resultFileContent" == "unsat" ]; then
                # echo "unsat"
                if [ ! $result ]; then
                    result="unsat"
                    resultCounter="1"
                elif [ $result == "unsat" ]; then
                    result="unsat"
                    resultCounter=$[$resultCounter + 1]
                else 
                    # echo "$solver" disagrees on result
                    exit
                fi
            else
                echo "error" for "$f"
                exit
            fi
        fi
    done;
#    echo overall result "$result" from "$resultCounter" tools
    if [ $resultCounter -gt 1 ]; then
        echo "$resultCounter" tools agreed on result: "$result"
        echo "$result" > "$f".results.txt
    else
        echo for "$f" I only have result from "$resultCounter" tool
    fi
done;

