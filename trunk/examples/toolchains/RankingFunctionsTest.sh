#!/bin/bash
# Test script for regression discovery
# in the Ultimate module "RankingFunctions"
#
# Written by Jan Leike July 2012
# Adapted from a script by Matthias Heizmann

if [ "`uname -m`" = "i686" ]; then
	arch="x86"
elif [ "`uname -m`" = "x86_64" ]; then
	arch="x86_64"
else
	echo "Unknown processor architecture."
	exit 1
fi


Ultimate_PATH=`pwd`;
UltimateEXE="trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/$arch/Ultimate";

TestDir="trunk/examples/rank/"
TOOLCHAIN="$Ultimate_PATH/trunk/examples/toolchains/RankSynthesizer.xml"

TimeLimit=60;

PASS_CODE="\e[0;32mOK.\e[00m"
FAIL_CODE="\e[0;31mFAIL.\e[00m"
WARN_CODE="\e[1;33m!?!?\e[00m"
NOSPEC_CODE="\e[1;33m(?)\e[00m"



echo "Started `date`."

files=`find "$TestDir" -name "*.bpl" | sort`

for f in $files; do
	echo -n "Test case: $f "

	KEYWORD_TERMD=`head -n 1 "$f" | grep "#rTerminationDerivable"`
	# program does terminate and Ultimate should see that
	KEYWORD_TERM=`head -n 1 "$f" | grep "#rTermination"`
	# program does terminate, but Ultimate might not see that
	KEYWORD_NTERM=`head -n 1 "$f" | grep "#rNontermination"`
	# program does not terminate
	KEYWORD_ERROR=`head -n 1 "$f" | grep "#rTerminationError"`
	# program will not be able to be processed

	# Run Ultimate!
	Ultimate_OUTPUT=`bash -c "ulimit -t $TimeLimit; $Ultimate_PATH/$Ultimate_BIN --console "$TOOLCHAIN" "$f" 2>&1"`

	EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "has thrown an Exception!"`
	EXCEPT=`echo "$Ultimate_OUTPUT" | grep "Exception"`
	ASSERTION_ERROR=`echo "$Ultimate_OUTPUT" | grep "java.lang.AssertionError"`

	RESULT_NORANKING=`echo "$Ultimate_OUTPUT" | grep "No ranking function has been found."`
	RESULT_RANKING=`echo "$Ultimate_OUTPUT" | grep "A ranking function has been found:"`

	if [ "$EXCEPT" -o "$ASSERTION_ERROR" -o "$JVMCRASH" ]; then
		if [ "$KEYWORD_ERROR" ]; then
			echo -e "$PASS_CODE"
			continue
		fi
		
		if [ "$EXCEPT" ]; then
			echo -e "$FAIL_CODE"
			echo "$EXCEPT"
			continue
		fi
		
		if [ "$ASSERTION_ERROR" ]; then 
			echo -e "$FAIL_CODE"
			echo "Assertion error"
			continue;
		fi
		
		if [ "$JVMCRASH" ]; then 
			echo -e "$FAIL_CODE"
			echo "$JVMCRASH"
			continue
		fi
	fi
	
	#echo "$Ultimate_OUTPUT" | grep "Statistics:" | cut -c67-
	#RUNTIME=`echo "$Ultimate_OUTPUT" | grep "RankingFunctions took" | cut -c73-`
	
	if [ "$RESULT_RANKING" ]; then
		if [ "$KEYWORD_TERMD" ]; then
			echo -e "$PASS_CODE"
			continue
		fi
		if [ "$KEYWORD_NTERM" ]; then
			echo -e "$FAIL_CODE"
			echo "Derived a ranking function for non-terminating loop."
			continue
		fi
		if [ "$KEYWORD_TERM" ]; then
			echo -e "$WARN_CODE"
			echo "Termination was unexpectedly proven!?!?"
			continue
		fi
		if [ "$KEYWORD_ERROR" ]; then
			echo -e "$WARN_CODE"
			echo "Expected failure, but no failure occured. I am confused. :/"
			continue
		fi
		echo -e "$NOSPEC_CODE"
		echo "Termination proven, but no specification was given."
		continue
	fi

	if [ "$RESULT_NORANKING" ]; then
		if [ "$KEYWORD_TERMD" ]; then
			echo -e "$FAIL_CODE"
			echo "Did not derive a ranking function although one should exist."
			continue
		fi
		if [ "$KEYWORD_TERM" -o "$KEYWORD_NTERM" ]; then
			echo -e "$PASS_CODE"
			continue
		fi
		if [ "$KEYWORD_ERROR" ]; then
		echo -e "$WARN_CODE"
			echo "Expected failure, but no failure occured. I am confused. :/"
			continue
		fi
		echo -e "$NOSPEC_CODE"
		echo "Termination not proven, but no specification was given."
		continue
	fi

	if [ "$KEYWORD_ERROR" ]; then
		echo -e "$WARN_CODE"
		echo "Expected failure, but no failure occured. I am confused. :/"
		continue
	fi

	echo -e "$FAIL_CODE"
	echo "Could not understand what Ultimate said."
	#echo "$Ultimate_OUTPUT"
done

echo "Finished `date`."

