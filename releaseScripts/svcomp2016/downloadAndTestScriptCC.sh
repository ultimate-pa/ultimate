#!/bin/bash
# Script for checking if Ultimate SV-COMP competition contributions are working.
# Date: 2014-11-04
# Author: Matthias Heizmann

function checkResult {
	echo $1|grep $2

}


wget --no-check-certificate https://ultimate.informatik.uni-freiburg.de/downloads/svcomp2016/UltimateKojak.zip
unzip UltimateKojak.zip
cd UltimateKojak
Tests=( \
### Memsafety
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/memory-alloca/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/memory-alloca/knapsack_alloca_unsafe_false-valid-deref.i;32bit;precise;FALSE(valid-deref)" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/memsafety/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/memsafety/test-0158_false-valid-free.i;32bit;precise;FALSE(valid-free)" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/list-ext-properties/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/list-ext-properties/test-0158_1_false-valid-memtrack.i;32bit;precise;FALSE(valid-memtrack)" \
### Control flow and integers
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/ssh-simplified/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/ssh-simplified/s3_clnt_1_true-unreach-call.cil.c;32bit;precise;TRUE" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/ssh-simplified/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/ssh-simplified/s3_clnt_1_false-unreach-call.cil.c;32bit;precise;FALSE" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/loop-acceleration/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/loop-acceleration/array_true-unreach-call3.i;32bit;precise;TRUE" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/loop-acceleration/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/loop-acceleration/simple_false-unreach-call2.i;32bit;precise;FALSE" \
### Bitvectors
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/bitvector/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/bitvector/byte_add_1_true-unreach-call.i;32bit;precise;UNKNOWN" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/bitvector/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/bitvector/jain_1_true-unreach-call.i;32bit;precise;TRUE" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/bitvector/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/bitvector-regression/implicitunsignedconversion_false-unreach-call.i;32bit;precise;FALSE" \
### Recursive
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/recursive/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/recursive/recHanoi02_true-unreach-call_true-termination.c;32bit;precise;TRUE" \
"https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/recursive/ALL.prp;https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/recursive/McCarthy91_false-unreach-call_false-termination.c;32bit;precise;FALSE" \
)

for quintuple in "${Tests[@]}"
do
	IFS=';' read -ra testArray <<< "$quintuple"
	testElements=${#testArray[@]}
	if [ "$testElements" != "5" ]; then
	    echo "Argument is no quintuple"
	    exit
	fi
	propertyUrl=${testArray[0]};
	property=`basename "$propertyUrl"`
    if [ -e "$property" ]; then
        echo "Property $property already  exists"
        exit
    fi
	fileUrl=${testArray[1]};
	file=`basename "$fileUrl"`
	if [ -e "$file" ]; then
        echo "File $file already  exists"
        exit
	fi
	bit=${testArray[2]};
	memMod=${testArray[3]};
	expectedResult=${testArray[4]};
	wget -q "$propertyUrl"
	wget -q "$fileUrl"
	echo "python Ultimate.py" "$property" "$file" "$bit" "$memMod"
	OUTPUT=`python Ultimate.py "$property" "$file" "$bit" "$memMod"`
	echo $OUTPUT
	TestResult=`checkResult "$OUTPUT" "$expectedResult"`
	if [ "$TestResult" ]
	then
		echo "Test passed"
	else
		echo "Test failed"
	fi
	rm "$file"
	rm "$property"
done
