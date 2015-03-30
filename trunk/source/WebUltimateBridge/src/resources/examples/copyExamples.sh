#!/bin/bash
# Author: Matthias Heizmann
# Date: 2014-07-13
#
# This bash script is in the folder
#    trunk/source/WebUltimateBridge/src/resources/examples
# The purpose of this script is to copy examples from
#    trunk/examples
# to this folder
# Files that are in certain subfolders (e.g., rankBoogie, rankC) of this folder 
# will be added to the web interface.
# Before I build a new version of the web interface I (Matthias) will execute
# this script.
# 


RANK_BOOGIE=(
# 	"../../../../../examples/lassos/website/ATVA2013-yPositive-int.bpl"
	"../../../../../examples/lassos/*.bpl"
	"../../../../../examples/lassos/website/*.bpl"
	"../../../../../examples/lassos/arrays/SyntaxSupportArrays08-LexIndexValue.bpl"
	)

for i in "${RANK_BOOGIE[@]}"
do
# 	if [ ! -e "$i" ]; then
# 		echo "cannot find $i"
# 		exit 1
# 	fi
	cp $i rankBoogie/
done


RANK_C=(
# 	"../../../../../examples/lassos/tigerbytes/ChenFlurMukhopadhyay-SAS2012-Ex1.01_true-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-TACAS2014-Ex1_true-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-TACAS2014-Ex7_true-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-TACAS2014-Ex8_true-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-TACAS2014-Ex9_true-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-TACAS2014-Fig1_true-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-WST2014-Ex5_false-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-WST2014-Ex6_false-termination.c"
# 	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/LeikeHeizmann-WST2014-Ex9_true-termination.c"
#	"../../../../../examples/termination/TermCompOfficialBenchmarkSet/svcomp/*.c"
	"../../../../../examples/svcomp/termination-crafted/*.c"
	"../../../../../examples/svcomp/termination-crafted-lit/*.c"
	)

for i in "${RANK_C[@]}"
do
# 	if [ ! -e "$i" ]; then
# 		echo "cannot find $i"
# 		exit 1
# 	fi
	cp $i rankC/
done


TERMINATION_BOOGIE=(
	"../../../../../examples/programs/termination/MicrosoftZuneBug_false-termination.bpl"
	"../../../../../examples/lassos/*.bpl"
	"../../../../../examples/lassos/website/*.bpl"
	"../../../../../examples/lassos/arrays/SyntaxSupportArrays08-LexIndexValue.bpl"
	)

for i in "${TERMINATION_BOOGIE[@]}"
do
# 	if [ ! -e "$i" ]; then
# 		echo "cannot find $i"
# 		exit 1
# 	fi
	cp $i terminationBoogie/
done




TERMINATION_C=(
	"../../../../../examples/programs/termination/Bubblesort_true-termination.c"
	"../../../../../examples/programs/termination/MicrosoftZuneBug_false-termination.c"
	"../../../../../examples/svcomp/termination-crafted/*.c"
	"../../../../../examples/svcomp/termination-crafted-lit/*.c"
	)

for i in "${TERMINATION_C[@]}"
do
# 	if [ ! -e "$i" ]; then
# 		echo "cannot find $i"
# 		exit 1
# 	fi
	cp $i terminationC/
done



VERIFY_C=(
	"../../../../../examples/programs/toy/website/*.c"
	)

for i in "${VERIFY_C[@]}"
do
# 	if [ ! -e "$i" ]; then
# 		echo "cannot find $i"
# 		exit 1
# 	fi
	cp $i verifyC/
done



VERIFY_BOOGIE=(
	"../../../../../examples/programs/toy/website/*.bpl"
	)

for i in "${VERIFY_BOOGIE[@]}"
do
# 	if [ ! -e "$i" ]; then
# 		echo "cannot find $i"
# 		exit 1
# 	fi
	cp $i verifyBoogie/
done