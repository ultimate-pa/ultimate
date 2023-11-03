#!/bin/bash

Ultimate_PATH=`pwd`;

assertionString=$1

if [[ "$assertionString" != "-da" && "$assertionString" != "-ea" ]]; then
	echo "first argument has to be -ea or -da"
	exit
fi

shift

timeout=$1;
if [[ $var =~ ^-?[0-9]+$ ]]; then
    echo "Timeout is not an integer"
    exit
fi

shift


examplesFolder=$1;
if [ ! -e "$examplesFolder" ]; then
    echo "Folder $examplesFolder does not exist"
    exit
fi

shift

triples=${@};
echo "$# triples"

c_Toolchain=
bpl_Toolchain=
settings=
# for triple in $triples
# do
#     IFS=';' read -ra tripleArray <<< "$triple"
#     tripleElements=${#tripleArray[@]}
#     if [ "$tripleElements" != "3" ]; then
#         echo "Argument is no triple of bpl-Toolchain, c-Toolchain, settings"
#         exit
#     fi
#     bpl_Toolchain=${tripleArray[0]};
#     echo $bpl_Toolchain
#     c_Toolchain=${tripleArray[1]};
#     echo $c_Toolchain
#     settings=${tripleArray[2]};
#     echo settings
# done


#------------------------------------------------------------------------------
# determine processor architecture string
#------------------------------------------------------------------------------
if [ "`uname -m`" = "i686" ]; then
	arch="x86"
elif [ "`uname -m`" = "x86_64" ]; then
	arch="x86_64"
else
	echo "Unknown processor architecture."
	exit 1
fi

#------------------------------------------------------------------------------
# assume that the executable is in following directory
#------------------------------------------------------------------------------
UltimateEXE="trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/$arch/Ultimate";
if [ ! -e "$UltimateEXE" ]; then
    echo "unable to find Ultimate executable $UltimateEXE"
    exit
fi


function setAssertions {
	#------------------------------------------------------------------------------
	# set enable assertions
	#------------------------------------------------------------------------------
	UltimateINI="trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/$arch/Ultimate.ini";
	if [ ! -e "$UltimateINI" ]; then
		echo "unable to find Ultimate.ini $UltimateINI"
		exit
	fi

oldAssertionString=
	# detect if -da is already set
	oldDA=`grep "\-da$" "$UltimateINI"`
	oldEA=`grep "\-ea$" "$UltimateINI"`
	if [ "$oldDA" ]; then
		echo "status of assertions before: -da"
		sed -i "s/-da$/$assertionString/g" "$UltimateINI"
	elif [ "$oldEA" ]; then
		echo "status of assertions before: -ea"
		sed -i "s/-ea$/$assertionString/g" "$UltimateINI"
	else 
		echo "assertions were not set before"
		echo "$assertionString" >> "$UltimateINI"
	fi
	echo "status of assertions now $assertionString"
}

setAssertions


cd "$examplesFolder"
#for f in `ls *.bpl`;
files=`find . -name "*.bpl" -o -name "*.c"|sort`

for f in $files;
do
    # stores if filename contains substring safe (resp. unsafe), is empty otherwise
    FILENAME_SAFE=`echo "$f" | grep -i "safe"`
    FILENAME_UNSAFE=`echo "$f" | grep -i "unsafe"`
    FILENAME_TRUE=`echo "$f" | grep -i "true-unreach-call"`
    FILENAME_FALSE=`echo "$f" | grep -i "false-unreach-call"`
    # stores the first line of $f if this line contains one of the following keywords, is empty otherwise
    KEYWORD_SYNTAX=`head -n 1 "$f" | grep "#Syntax"`
    KEYWORD_SAFE=`head -n 1 "$f" | grep "#Safe"`
    KEYWORD_UNSAFE=`head -n 1 "$f" | grep "#Unsafe"`
    VCCPRELUDE=`head -n 1 "$f" | grep "#VccPrelude"`

    # stores "1" if program is safe (resp. unsafe), is empty otherwise
    PROGRAM_SAFE=
    PROGRAM_UNSAFE=
    WHO_DEFINED_SOLUTION="No solution given. "
    
    if [ "$FILENAME_SAFE" ]; then
		WHO_DEFINED_SOLUTION="Solution given by filename is: "
		if [ "$FILENAME_UNSAFE" ]; then
			PROGRAM_UNSAFE="1"
		else
			PROGRAM_SAFE="1"
		fi
	else 
		if [ "$FILENAME_TRUE" ]; then 
		WHO_DEFINED_SOLUTION="Solution given by filename is: "
		PROGRAM_SAFE="1"
		PROGRAM_UNSAFE=
		fi

		if [ "$FILENAME_FALSE" ]; then 
		WHO_DEFINED_SOLUTION="Solution given by filename is: "
		PROGRAM_SAFE=
		PROGRAM_UNSAFE="1"
		fi
		
		if [ "$KEYWORD_SAFE" ]; then 
		WHO_DEFINED_SOLUTION="Solution given by EvrenKeyword is: "
		PROGRAM_SAFE="1"
		PROGRAM_UNSAFE=
		fi

		if [ "$KEYWORD_UNSAFE" ]; then 
		WHO_DEFINED_SOLUTION="Solution given by EvrenKeyword is: "
		PROGRAM_SAFE=
		PROGRAM_UNSAFE="1"
		fi
    fi

    for triple in $triples
    do
	IFS=';' read -ra tripleArray <<< "$triple"
	tripleElements=${#tripleArray[@]}
	if [ "$tripleElements" != "3" ]; then
	    echo "Argument is no triple of bpl-Toolchain, c-Toolchain, settings"
	    exit
	fi
	bpl_Toolchain=${tripleArray[0]};
	#echo $bpl_Toolchain
	c_Toolchain=${tripleArray[1]};
	#echo $c_Toolchain
	settings=${tripleArray[2]};
	#echo $settings
	
	EXTENSION=${f##*.}
	TOOLCHAIN="unset"
	if [ "$EXTENSION" == "bpl" ]; then
	    TOOLCHAIN="$Ultimate_PATH/trunk/examples/toolchains/$bpl_Toolchain"
	fi

	if [ "$EXTENSION" == "c" ]; then
	    TOOLCHAIN="$Ultimate_PATH/trunk/examples/toolchains/$c_Toolchain"
	fi
	
	SETTINGS="$Ultimate_PATH/trunk/examples/settings/$settings"
	
	if [ ! -e "$TOOLCHAIN" ]; then
	    echo "Toolchain does not exist $TOOLCHAIN"
	    exit
	fi
	
	if [ ! -e "$SETTINGS" ]; then
	    echo "Settings does not exist $settings"
	    exit
	fi
	
	#Ultimate_OUTPUT=`$Ultimate_PATH/console/eclipse/Ultimate --console $Ultimate_PATH/examples/toolchains/TraceAbstraction.xml $f --prelude $Ultimate_PATH/examples/VCC/VccPrelude.bpl --settings $Ultimate_PATH/examples/toolchains/TraceAbstractionLowTheoremProverUsage.settings 2>&1`

	start=`date +%s`
	if [ "$VCCPRELUDE" ]; then 
	    Ultimate_OUTPUT=`bash -c "ulimit -t $timeout; $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$f" --prelude "$Ultimate_PATH/trunk/examples/programs/translated-vcc/Vcc2Prelude.bpl" --settings "$SETTINGS" 2>&1"`    
	else
	    # echo $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$examplesFolder/$f" --settings "$SETTINGS"
	    Ultimate_OUTPUT=`bash -c "ulimit -t $timeout; $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$f" --settings "$SETTINGS" 2>&1"`
	fi
	end=`date +%s`

	USED_SETTINGS=`echo "$Ultimate_OUTPUT" | grep "ettings: "`
	EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "has thrown an Exception!"`
	EXCEPT=`echo "$Ultimate_OUTPUT" | grep "Exception\|AssertionError"`
	Z3CRASH1=`echo "$Ultimate_OUTPUT" | grep "libz3-gmp.so"`
	Z3CRASH2=`echo "$Ultimate_OUTPUT" | grep "double free or corruption"`
	#echo "$Ultimate_OUTPUT"
	RESULT_SAFE=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate proved your program to be correct!\|We were not able to verify any specifiation because the program does not contain any specification.\|We were not able to verify any specification because the program does not contain any specification."`
	RESULT_UNSAFE=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate proved your program to be incorrect!"`
	RESULT_SYNTAX=`echo "$Ultimate_OUTPUT" | egrep "RESULT:\ Ultimate\ could\ not\ prove\ your\ program:\ Incorrect\ Syntax|RESULT:\ Ultimate\ could\ not\ prove\ your\ program:\ Type\ Error"`
	UNSUPPORTED_SYNTAX=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate could not prove your program: Unsupported Syntax"`
	RESULT_TIMEOUT=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate could not prove your program: Timeout"`
	RESULT_UNKNOWN=`echo "$Ultimate_OUTPUT" | grep "Unable to decide correctness. Please check the following counterexample manually."`
	RESULT_INSUFFICIENT_ITERATIONS=`echo "$Ultimate_OUTPUT" | grep -c "RESULT: Ultimate could not prove your program: Insufficient iterations to proof correctness"`
	RESULT_NORESULT=`echo "$Ultimate_OUTPUT" | grep -c "RESULT: Ultimate could not prove your program: Toolchain returned no Result."`
	RESULT_PROVEN_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Buchi Automizer proved that your program is terminating"`
	RESULT_UNKNOWN_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Buchi Automizer was unable to decide termination"`
	RESULT_FALSE_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Nonterminating execution"`
	BUG_24=`echo "$Ultimate_OUTPUT" | grep "at de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.addClause(ConvertFormula.java:349)"`
	BUG_14=`echo "$Ultimate_OUTPUT" | grep "at de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.convertFormula(ConvertFormula.java:"`
	BUG_22=`echo "$Ultimate_OUTPUT" | grep "java.lang.AssertionError: Z3 says unsat, SmtInterpol says sat!"`
	PARSE_ERROR=`echo "$Ultimate_OUTPUT" | grep "ERROR \[Parser.java"`
	ARRAY_ERROR=`echo "$Ultimate_OUTPUT" | grep "java.lang.IllegalArgumentException: Solver does not support arrays"`
	PRELUDE_ERROR=`echo "$Ultimate_OUTPUT" | grep " which has not been decleared before"`
	TYPE_ERROR=`echo "$Ultimate_OUTPUT" | grep "ERROR \[TypeManager.java"`
	OOM_HEAP=`echo "$Ultimate_OUTPUT" | grep "java.lang.OutOfMemoryError: Java heap space"`
	OOM_GC=`echo "$Ultimate_OUTPUT" | grep "java.lang.OutOfMemoryError: GC overhead limit exceeded"`
	Z3ERROR7=`echo "$Ultimate_OUTPUT" | grep "Z3 error 7: unknown"`
	Z3ERROR=`echo "$Ultimate_OUTPUT" | grep "terminate called after throwing an instance of 'z3error'"`
	ASSERTION_ERROR=`echo "$Ultimate_OUTPUT" | grep "java.lang.AssertionError"`
	KILLED=`echo "$Ultimate_OUTPUT" | grep "KILLED"`
	JVMCRASH=`echo "$Ultimate_OUTPUT" | grep "A fatal error has been detected by the Java Runtime Environment"`
	Z3NativeCodeException=`echo "$Ultimate_OUTPUT" | grep "de.uni_freiburg.informatik.ultimate.nativez3.NativeCodeException: Did not find object in hashmap"`



	INITIALIZED=`echo "$Ultimate_OUTPUT" | grep "Initializing TraceAbstraction..."`
	#echo "$RESULT_CORRECT"

	printf "Program: " 
	printf "$f"
	printf " Toolchain: "
	printf "$TOOLCHAIN"
	printf "  Settings File: "
	printf "$settings"
	printf "\n"
	if [ "$USED_SETTINGS" ]; then
	  echo $USED_SETTINGS
	fi


	if [ "$EXCEPT" ]; then
	    echo "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11"
	    echo "$EXCEPT"
	    echo "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11"
	fi

	if [ "$KILLED" ]; then 
	    echo "!!!Killed!!!";
	    continue;
	fi

	if [ "$Z3CRASH1" ]; then 
	    echo "!!!FAIL!!! Abnormal Z3 termination: $Z3CRASH1";
	    continue;
	fi

	if [ "$Z3CRASH2" ]; then 
	    echo "!!!FAIL!!! Abnormal Z3 termination: $Z3CRASH2";
	    continue;
	fi

	if [ "$Z3ERROR7" ]; then 
	    echo "!!!FAIL!!! $Z3ERROR7";
	    continue;
	fi

	if [ "$Z3ERROR" ]; then 
	    echo "!!!FAIL!!! $Z3ERROR";
	    continue;
	fi

	if [ "$Z3Z3NativeCodeException" ]; then 
	    echo "!!!FAIL!!! $Z3NativeCodeException";
	    continue;
	fi


	if [ "$BUG_22" ]; then 
	    echo "!!!FAIL!!! $BUG_22";
	    continue;
	fi

	if [ "$BUG_24" ]; then 
	    echo "!Warning! AssertionError - Probably Bug #24 "$'\n'
	    continue;
	fi


	if [ "$EXCEPTION"  ]; then
	    if [ "$PRELUDE_ERROR" ]; then
		echo "!Warning! Exception thrown - Undeclared variable - Forgotten to load VCC Prelude? "$'\n'
		continue;
	    fi
	    if [ "$TYPE_ERROR" ]; then
		echo "!Warning! Exception thrown - Type Error - Forgotten to load VCC Prelude? "$'\n'
		continue;
	    fi
	    if [ "$BUG_14" ]; then
		echo "!Warning! Exception thrown - Probably Bug #14 "$'\n'
		continue;
	    fi
	    if [ "$ARRAY_ERROR" ]; then
		echo "!Warning! Exception thrown - $ARRAY_ERROR "$'\n'
		continue;
	    fi
	    if [ "$OOM_HEAP" ]; then
		echo "!Warning! Exception thrown - $OOM_HEAP "$'\n'
		continue;
	    fi
	    if [ "$OOM_GC" ]; then
		echo "!Warning! Exception thrown - $OOM_GC "$'\n'
		continue;
	    fi
	    echo "!!!FAIL!!! Exception thrown"$'\n'
	    continue;
	else 
	    if [ "$OOM_HEAP" ]; then
		echo "!Warning! $OOM_HEAP "$'\n'
		continue;
	    fi
	    if [ "$OOM_GC" ]; then
		echo "!Warning! $OOM_GC "$'\n'
		continue;
	    fi
	fi 

	if [ "$ASSERTION_ERROR" ]; then 
	    echo "!!!FAIL!!! $ASSERTION_ERROR";
	    continue;
	fi

	if [ "$JVMCRASH" ]; then 
	    echo "!!!FAIL!!! $JVMCRASH";
	    continue;
	fi


	echo "$Ultimate_OUTPUT" | grep "Statistics:" | cut -c67-
	echo "$Ultimate_OUTPUT" | grep -A 1 "BenchmarkResult:" | cut -c60-
    TOTALRUNTIME=$(($end - $start))
    #`echo "$Ultimate_OUTPUT" | tail -n 3 | grep "real" | cut -c6-`

	if [ "$RESULT_SYNTAX" ]; then
	    if [ "$KEYWORD_SYNTAX" ]; then
		printf "Success."
		printf "Ultimate says: Syntax error. "
		printf "$WHO_DEFINED_SOLUTION Syntax error.\n"
		continue;
	    fi
	    if [ "$PROGRAM_UNSAFE" -o "$PROGRAM_SAFE" -o "$VCCPRELUDE" ]; then
		printf "!!!FAIL!!! "
		printf "Ultimate says: Syntax error. "
		printf "Solution does not mention any syntax errors \n"
		continue;
	    fi
	    printf "!Warning! "
	    printf "Ultimate says: Syntax error. "
	    printf "$WHO_DEFINED_SOLUTION\n"
	    continue;
	fi


	if [ "$UNSUPPORTED_SYNTAX" ]; then
	    printf "!Warning! "
	    printf "Ultimate says: Unsupported syntax.\n"
	    continue;
	fi

	if [ "$RESULT_TIMEOUT" ]; then
	    printf "!Warning! "
	    printf "Ultimate terminated after $TOTALRUNTIME and says: Timeout.\n"
	    continue;
	fi


	if [ "$RESULT_SAFE" ]; then
	    if [ "$PROGRAM_SAFE" ]; then
		printf "Success. "
		printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Program is safe. "
		printf "$WHO_DEFINED_SOLUTION Program is safe.\n"
		continue;
	    fi
	    if [ "$PROGRAM_UNSAFE" ]; then
		printf "!!!FAIL!!! "
		printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Program is safe. "
		printf "$WHO_DEFINED_SOLUTION Program is unsafe.\n"
		continue;
	    fi
	    printf "!Warning! "
	    printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Program is safe. "
	    printf "$WHO_DEFINED_SOLUTION \n"
	    continue;
	fi

	if [ "$RESULT_UNSAFE" ]; then
	    if [ "$PROGRAM_UNSAFE" ]; then
		printf "Success. "
		printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Program is unsafe. "
		printf "$WHO_DEFINED_SOLUTION Program is unsafe.\n"
		continue;
	    fi
	    if [ "$PROGRAM_SAFE" ]; then
		printf "!!!FAIL!!! "
		printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Program is unsafe. "
		printf "$WHO_DEFINED_SOLUTION Program is safe.\n"
		continue;
	    fi
	    printf "!Warning! "
	    printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Program is unsafe. "
	    printf "$WHO_DEFINED_SOLUTION \n"
	    continue;
	fi

	if [ "$RESULT_UNKNOWN" ]; then
	    if [ "$PROGRAM_UNSAFE" ]; then
		printf "!Warning!"
		printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Can not determine feasibility of counterexample."
		printf "$WHO_DEFINED_SOLUTION Program is unsafe.\n"
		continue;
	    fi
	    if [ "$PROGRAM_SAFE" ]; then
		printf "!Warning! "
		printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Can not determine feasibility of counterexample."
		printf "$WHO_DEFINED_SOLUTION Program is safe.\n"
		continue;
	    fi
	    printf "!Warning! "
	    printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Can not determine feasibility of counterexample."
	    printf "$WHO_DEFINED_SOLUTION \n"
	    continue;
	fi

	if [ "$RESULT_UNKNOWN" ]; then
	    printf "!Warning! "
	    printf "TraceAbstraction terminated after $TOTALRUNTIME and says: Insufficient iterations. \n"
	    continue;
	fi
	
	if [ "$RESULT_PROVEN_TERMINATION" ]; then
        printf "Buchi Automizer terminated after $TOTALRUNTIME and says: Termination proven \n"
        printf "$RESULT_PROVEN_TERMINATION \n"
        continue;
    fi
    
     if [ "$RESULT_FALSE_TERMINATION" ]; then
        printf "Buchi Automizer terminated after $TOTALRUNTIME and says: Nontermination possible \n"
        printf "$RESULT_FALSE_TERMINATION \n"
        continue;
    fi
    
    if [ "$RESULT_UNKNOWN_TERMINATION" ]; then
        printf "Buchi Automizer terminated after $TOTALRUNTIME and says: Unable to decide termination \n"
        printf "$RESULT_UNKNOWN_TERMINATION \n"
        continue;
    fi

	if [ "$RESULT_NORESULT" ]; then
	    printf "!Warning! "
	    printf "Ultimate Automizer terminated after $TOTALRUNTIME and says: No Result. \n"
	    
	    continue;
	fi





	if [ "$INITIALIZED" ]; then
	      printf "!!!FAIL!!! started Ultimate, received no answer after $timeout seconds \n"
	    else
	      printf "!!!FAIL!!! unknown program behaviour \n"
	fi

    done;
    echo "";
done;
cd -
