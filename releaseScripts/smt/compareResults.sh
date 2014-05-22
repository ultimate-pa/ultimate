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
solvers[1]="SMTInterpol"
#solvers[2]="Mathsat"
#solvers[2]="CVC4"
#solvers[0]="z3"
echo "Solvers: ${solvers[*]}"
#solverCommands[1]="z3 SMTLIB2_COMPLIANT=true -t:5000"
#solverCommands[2]="java -jar /opt/SMTInterpol/smtinterpol.jar -q -no-success"
solverCommands[0]="veriT"


for f in `find "$examplesFolder" -name "*.smt2"`;
do

resultFileFirstSolver="$f".${solvers[0]}_results.txt
if [ ! -e "$resultFileFirstSolver" ]; then
    echo "File $resultFileFirstSolver does not exist"
    exit
fi
if [ ! -s "$resultFileFirstSolver" ]; then
    echo "File $resultFileFirstSolver is empty"
    exit
fi

for((i=1;i<${#solvers[@]};i++))
do
    #echo Solver ${solvers[$i]}
    solver=${solvers[$i]}
    resultFileOtherSolver="$f".${solvers[i]}_results.txt
    if [ ! -e "$resultFileOtherSolver" ]; then
        echo "File $resultFileOtherSolver does not exist"
        #exit
    else 
      differ=`diff "$resultFileFirstSolver" "$resultFileOtherSolver"`
      if [ "$differ" ]; then
          echo "$solver" does not agree on result for "$f"
      else 
          resultFile="$f".results.txt
          echo writing "$resultFile"
          cp "$resultFileFirstSolver" "$resultFile"
      fi
    fi
    
#   solverCommand=${solverCommands[$i]}
#   for f in `find "$examplesFolder" -name "*.smt2"`;
#   do
#   resultFile="$f"."$solver"_results.txt
#   if [ -e $resultFile ]; then
#       echo "result file $resultFile already exists"
#   else
#       echo "$solverCommand $f"
#       eval $solverCommand "$f" |grep -v success > "$resultFile"
#   fi
    done;


done;

# done;
