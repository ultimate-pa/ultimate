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
solvers[2]="Mathsat"
echo "Solvers: ${solvers[*]}"
solverCommands[1]="z3 SMTLIB2_COMPLIANT=true -t:5000"
solverCommands[2]="java -jar /opt/SMTInterpol/smtinterpol.jar -q -no-success"
solverCommands[3]="mathsat < "


for((i=0;i<${#solvers[@]};i++))
do
	echo Solver ${solvers[$i]}
	solver=${solvers[$i]}
	solverCommand=${solverCommands[$i]}
	for f in `find "$examplesFolder" -name "*.smt2"`;
	do
	resultFile="$f"."$solver"_results.txt
	if [ -e $resultFile ]; then
		echo "result file $resultFile already exists"
	else
		echo "$solverCommand $f"
		eval $solverCommand "$f" |grep -v success > "$resultFile"
	fi
	done;
done;
