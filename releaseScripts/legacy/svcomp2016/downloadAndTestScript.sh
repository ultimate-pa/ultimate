#!/bin/bash
# Script for checking if Ultimate SV-COMP competition contributions are working.
# Date: 2014-11-04
# Author: Matthias Heizmann

function checkResult {
	echo $1|grep $2

}


wget --no-check-certificate https://ultimate.informatik.uni-freiburg.de/downloads/svcomp2016/UltimateAutomizer.zip
unzip UltimateAutomizer.zip
cd UAutomizer
Tests=( \
# "https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/;32bit;precise;FALSE(valid-deref)" \
### Memsafety Deref
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/array-memsafety/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/array-memsafety/diff_usafe_false-valid-deref.i;32bit;precise;FALSE(valid-deref)" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/array-memsafety/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/array-memsafety/array02-alloca_true-valid-memsafety.i;32bit;precise;TRUE(valid-deref)" \
### Memsafety DerefFreeMemtrack
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/memsafety/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/memsafety/test-0158_false-valid-free.i;32bit;precise;FALSE(valid-free)" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/list-ext-properties/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/list-ext-properties/test-0158_1_false-valid-memtrack.i;32bit;precise;FALSE(valid-memtrack)" \
### Integer Overflow
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/signedintegeroverflow-regression/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/signedintegeroverflow-regression/ConversionToSignedInt_true-no-overflow.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/signedintegeroverflow-regression/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/signedintegeroverflow-regression/AdditionIntMin_false-no-overflow.c.i;64bit;precise;FALSE" \
### Control flow and integers
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/ssh-simplified/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/ssh-simplified/s3_clnt_1_true-unreach-call.cil.c;32bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/ssh-simplified/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/ssh-simplified/s3_clnt_1_false-unreach-call.cil.c;32bit;precise;FALSE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/loop-acceleration/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/loop-acceleration/array_true-unreach-call3.i;32bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/loop-acceleration/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/loop-acceleration/simple_false-unreach-call2.i;32bit;precise;FALSE" \
### Bitvectors
# "https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/bitvector/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/bitvector/byte_add_1_true-unreach-call.i;32bit;precise;UNKNOWN" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/bitvector/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/bitvector/jain_1_true-unreach-call.i;32bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/bitvector/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/bitvector-regression/implicitunsignedconversion_false-unreach-call.i;32bit;precise;FALSE" \
### Recursive
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/recursive/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/recursive/recHanoi02_true-unreach-call_true-termination.c;32bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/recursive/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/recursive/McCarthy91_false-unreach-call_false-termination.c;32bit;precise;FALSE" \
### Termination
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/a.04-alloca_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/svcomp/termination-15/array06_alloca_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-15/cstrcat_mixed_alloca_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-15/cstrncat_malloc_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-crafted-lit/ChenFlurMukhopadhyay-SAS2012-Ex3.02_false-termination.c;64bit;precise;FALSE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/b.12-alloca_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/openbsd_cstrcpy-alloca_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-restricted-15/AlternKonv_false-termination.c;64bit;precise;FALSE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-restricted-15/DivMinus2_true-termination.c;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-libowfat/atoi_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-libowfat/strcasecmp_true-termination.c.i;64bit;precise;TRUE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-crafted/NonTermination2_false-termination.c;64bit;precise;FALSE" \
"https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-memory-alloca/ALL.prp;https://raw.githubusercontent.com/dbeyer/sv-benchmarks/master/c/termination-crafted/Collatz_unknown-termination.c;64bit;precise;UNKNOWN" \
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
	#echo $OUTPUT
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
