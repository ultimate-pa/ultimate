#!/bin/bash
Ultimate_PATH=`pwd`;

Coverage_Args="-vmargs --javaagent:integration-tests/jacoco/jacocoagent.jar=destfile=integration-tests/jacoco-it.exec"

timeout=$1;
if [[ $var =~ ^-?[0-9]+$ ]]; then
    echo "Timeout is not an integer"
fi

shift


examplesFolder=$1;
if [ ! -e "$examplesFolder" ]; then
    echo "Folder $examplesFolder does not exist"
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
UltimateEXE="source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/$arch/Ultimate";
if [ ! -e "$UltimateEXE" ]; then
    echo "unable to find Ultimate executable $UltimateEXE"
    exit
fi

cd "$examplesFolder"
#for f in `ls *.bpl`;
files=`find . -name "*.bpl" -o -name "*.c"|sort`

# FILE: file output
OUTTEXT=""

# FILE: counters
C_EXCEPT=0
C_Z3CRASH1=0
C_KILLED=0
C_Z3CRASH1=0
C_Z3CRASH2=0
C_Z3ERROR7=0
C_Z3ERROR=0
C_Z3Z3NativeCodeException=0
C_BUG_22=0
C_BUG_24=0
C_EXCEPTION=0
C_OOM_HEAP=0
C_OOM_GC=0
C_ASSERTION_ERROR=0
C_JVMCRASH=0
C_RESULT_SYNTAX_GOOD=0
C_RESULT_SYNTAX_BAD=0
C_RESULT_SYNTAX_UNKNOWN=0
C_UNSUPPORTED_SYNTAX=0
C_RESULT_TIMEOUT=0
C_RESULT_SUCCESS=0
C_RESULT_INVERTED=0
C_RESULT_STRANGE=0
C_RESULT_UNKNOWN=0
C_RESULT_NORESULT=0
C_INITIALIZED=0
C_UNKNOWN_ERROR=0

for f in $files;
do
    # FILE: file name
    OUTTEXT+="$f, ";
    
    # stores if filename contains substring safe (resp. unsafe), is empty otherwise
    FILENAME_SAFE=`echo "$f" | grep -i "safe"`
    FILENAME_UNSAFE=`echo "$f" | grep -i "unsafe"`
    FILENAME_TRUE=`echo "$f" | grep -i "true"`
    FILENAME_FALSE=`echo "$f" | grep -i "false"`
    # stores the first line of $f if this line contains one of the following keywords, is empty otherwise
    KEYWORD_SYNTAX=`head -n 1 "$f" | grep "#Syntax"`
    KEYWORD_MSAFE=`head -n 1 "$f" | grep "#mSafe"`
    KEYWORD_MUNSAFE=`head -n 1 "$f" | grep "#mUnsafe"`
    KEYWORD_ISAFE=`head -n 1 "$f" | grep "#iSafe"`
    KEYWORD_IUNSAFE=`head -n 1 "$f" | grep "#iUnsafe"`
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
                
                if [ "$KEYWORD_MSAFE" ]; then 
                WHO_DEFINED_SOLUTION="Solution given by EvrenKeyword is: "
                PROGRAM_SAFE="1"
                PROGRAM_UNSAFE=
                fi

                if [ "$KEYWORD_MUNSAFE" ]; then 
                WHO_DEFINED_SOLUTION="Solution given by EvrenKeyword is: "
                PROGRAM_SAFE=
                PROGRAM_UNSAFE="1"
                fi

                if [ "$KEYWORD_ISAFE" ]; then 
                WHO_DEFINED_SOLUTION="Solution given by EvrenKeyword is: "
                PROGRAM_SAFE="1"
                PROGRAM_UNSAFE=
                fi

                if [ "$KEYWORD_IUNSAFE" ]; then 
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
            TOOLCHAIN="$Ultimate_PATH/examples/toolchains/$bpl_Toolchain"
        fi

        if [ "$EXTENSION" == "c" ]; then
            TOOLCHAIN="$Ultimate_PATH/examples/toolchains/$c_Toolchain"
        fi
        
        SETTINGS="$Ultimate_PATH/examples/settings/$settings"
        
        if [ ! -e "$TOOLCHAIN" ]; then
            echo "Toolchain does not exist $TOOLCHAIN"
            exit
        fi
        
        if [ ! -e "$SETTINGS" ]; then
            echo "Settings does not exist $settings"
            exit
        fi
        
        #Ultimate_OUTPUT=`$Ultimate_PATH/console/eclipse/Ultimate --console $Ultimate_PATH/examples/toolchains/TraceAbstraction.xml $f --prelude $Ultimate_PATH/examples/VCC/VccPrelude.bpl --settings $Ultimate_PATH/examples/toolchains/TraceAbstractionLowTheoremProverUsage.settings 2>&1`

        if [ "$VCCPRELUDE" ]; then 
            Ultimate_OUTPUT=`bash -c "ulimit -t $timeout; $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$f" --prelude "$Ultimate_PATH/examples/programs/translated-vcc/Vcc2Prelude.bpl" --settings "$SETTINGS" $Coverage_Args 2>&1"`    
        else
            # echo $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$examplesFolder/$f" --settings "$SETTINGS"
            Ultimate_OUTPUT=`bash -c "ulimit -t $timeout; $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$f" --settings "$SETTINGS" $Coverage_Args 2>&1"`
        fi

        USED_SETTINGS=`echo "$Ultimate_OUTPUT" | grep "ettings: "`
        EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "has thrown an Exception!"`
        EXCEPT=`echo "$Ultimate_OUTPUT" | grep "Exception"`
        Z3CRASH1=`echo "$Ultimate_OUTPUT" | grep "libz3-gmp.so"`
        Z3CRASH2=`echo "$Ultimate_OUTPUT" | grep "double free or corruption"`
        #echo "$Ultimate_OUTPUT"
        RESULT_SAFE=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate proved your program to be correct!"`
        RESULT_UNSAFE=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate proved your program to be incorrect!"`
        RESULT_SYNTAX=`echo "$Ultimate_OUTPUT" | egrep "RESULT:\ Ultimate\ could\ not\ prove\ your\ program:\ Incorrect\ Syntax|RESULT:\ Ultimate\ could\ not\ prove\ your\ program:\ Type\ Error"`
        UNSUPPORTED_SYNTAX=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate could not prove your program: Unsupported Syntax"`
        RESULT_TIMEOUT=`echo "$Ultimate_OUTPUT" | grep "RESULT: Ultimate could not prove your program: Timeout"`
        RESULT_UNKNOWN=`echo "$Ultimate_OUTPUT" | grep "Program might be incorrect, check conterexample."`
        RESULT_INSUFFICIENT_ITERATIONS=`echo "$Ultimate_OUTPUT" | grep -c "RESULT: Ultimate could not prove your program: Insufficient iterations to proof correctness"`
        RESULT_NORESULT=`echo "$Ultimate_OUTPUT" | grep -c "RESULT: Ultimate could not prove your program: Toolchain returned no Result."`
        RESULT_PROVEN_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Ultimate Buchi Automizer: Termination proven."`
        RESULT_NOTPROVEN_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Ultimate Buchi Automizer: Unable to prove termination. Nonterminating?"`
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
        #printf " Toolchain: "
        #printf "$TOOLCHAIN"
        #printf "  Settings File: "
        #printf "$settings"
        #printf "\n"
        #if [ "$USED_SETTINGS" ]; then
        #  echo $USED_SETTINGS
        #fi
        printf "\n"


        if [ "$EXCEPT" ]; then
            OUTTEXT+="-EXCEPT, "
            C_EXCEPT=`expr $C_EXCEPT + 1`
            echo "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11"
            echo "$EXCEPT"
            echo "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11"
        fi

        if [ "$KILLED" ]; then
            OUTTEXT+="-KILLED, "
            C_KILLED=`expr $C_KILLED + 1`
            echo "!!!Killed!!!";
            
            continue;
        fi

        if [ "$Z3CRASH1" ]; then
            OUTTEXT+="-Z3CRASH1, "
            C_Z3CRASH1=`expr $C_Z3CRASH1 + 1`
            echo "!!!FAIL!!! Abnormal Z3 termination: $Z3CRASH1";
            continue;
        fi

        if [ "$Z3CRASH2" ]; then
            OUTTEXT+="-Z3CRASH2, "
            C_Z3CRASH2=`expr $C_Z3CRASH2 + 1`
            echo "!!!FAIL!!! Abnormal Z3 termination: $Z3CRASH2";
            continue;
        fi

        if [ "$Z3ERROR7" ]; then
            OUTTEXT+="-Z3ERROR7, "
            C_Z3ERROR7=`expr $C_Z3ERROR7 + 1`
            echo "!!!FAIL!!! $Z3ERROR7";
            continue;
        fi

        if [ "$Z3ERROR" ]; then
            OUTTEXT+="-Z3ERROR, "
            C_Z3ERROR=`expr $C_Z3ERROR + 1`
            echo "!!!FAIL!!! $Z3ERROR";
            continue;
        fi

        if [ "$Z3Z3NativeCodeException" ]; then
            OUTTEXT+="-Z3Z3NativeCodeException, "
            C_Z3Z3NativeCodeException=`expr $C_Z3Z3NativeCodeException + 1`
            echo "!!!FAIL!!! $Z3NativeCodeException";
            continue;
        fi


        if [ "$BUG_22" ]; then
            OUTTEXT+="-BUG_22, "
            C_BUG_22=`expr $C_BUG_22 + 1`
            echo "!!!FAIL!!! $BUG_22";
            continue;
        fi

        if [ "$BUG_24" ]; then
            OUTTEXT+="-BUG_24, "
            C_BUG_24=`expr $C_BUG_24 + 1`
            echo "!Warning! AssertionError - Probably Bug #24";
            continue;
        fi


        if [ "$EXCEPTION"  ]; then
            OUTTEXT+="-EXCEPTION, "
            C_EXCEPTION=`expr $C_EXCEPTION + 1`
            if [ "$PRELUDE_ERROR" ]; then
                echo "!Warning! Exception thrown - Undeclared variable - Forgotten to load VCC Prelude?"
                continue;
            fi
            if [ "$TYPE_ERROR" ]; then
                echo "!Warning! Exception thrown - Type Error - Forgotten to load VCC Prelude?"
                continue;
            fi
            if [ "$BUG_14" ]; then
                echo "!Warning! Exception thrown - Probably Bug #14"
                continue;
            fi
            if [ "$ARRAY_ERROR" ]; then
                echo "!Warning! Exception thrown - $ARRAY_ERROR"
                continue;
            fi
            if [ "$OOM_HEAP" ]; then
                echo "!Warning! Exception thrown - $OOM_HEAP"
                continue;
            fi
            if [ "$OOM_GC" ]; then
                echo "!Warning! Exception thrown - $OOM_GC"
                continue;
            fi
            echo "!!!FAIL!!! Exception thrown";
            continue;
        else
            if [ "$OOM_HEAP" ]; then
                OUTTEXT+="-OOM_HEAP, "
            C_OOM_HEAP=`expr $C_OOM_HEAP + 1`
                echo "!Warning! $OOM_HEAP"
                continue;
            fi
            if [ "$OOM_GC" ]; then
                OUTTEXT+="-OOM_GC, "
            C_OOM_GC=`expr $C_OOM_GC + 1`
                echo "!Warning! $OOM_GC"
                continue;
            fi
        fi 

        if [ "$ASSERTION_ERROR" ]; then
            OUTTEXT+="-ASSERTION_ERROR, "
            C_ASSERTION_ERROR=`expr $C_ASSERTION_ERROR + 1`
            echo "!!!FAIL!!! $ASSERTION_ERROR";
            continue;
        fi

        if [ "$JVMCRASH" ]; then 
            OUTTEXT+="-JVMCRASH, "
            C_JVMCRASH=`expr $C_JVMCRASH + 1`
            echo "!!!FAIL!!! $JVMCRASH";
            continue;
        fi


        echo "$Ultimate_OUTPUT" | grep "Statistics:" | cut -c67-
        RUNTIME=`echo "$Ultimate_OUTPUT" | grep "TraceAbstraction took" | cut -c73-`

        if [ "$RESULT_SYNTAX" ]; then
            if [ "$KEYWORD_SYNTAX" ]; then
                OUTTEXT+="+syntax_error, "
                C_C_RESULT_SYNTAX_GOOD=`expr $C_C_RESULT_SYNTAX_GOOD + 1`
                printf "Success."
                printf "Ultimate says: Syntax error. "
                printf "$WHO_DEFINED_SOLUTION Syntax error.\n"
                continue;
            fi
            if [ "$PROGRAM_UNSAFE" -o "$PROGRAM_SAFE" -o "$VCCPRELUDE" ]; then
                OUTTEXT+="-syntax_error, "
                C_C_RESULT_SYNTAX_BAD=`expr $C_C_RESULT_SYNTAX_BAD + 1`
                printf "!!!FAIL!!! "
                printf "Ultimate says: Syntax error. "
                printf "Solution does not mention any syntax errors \n"
                continue;
            fi
            OUTTEXT+="?syntax_error, "
            C_RESULT_SYNTAX_UNKNOWN=`expr $C_RESULT_SYNTAX_UNKNOWN + 1`
            printf "!Warning! "
            printf "Ultimate says: Syntax error. "
            printf "$WHO_DEFINED_SOLUTION\n"
            continue;
        fi


        if [ "$UNSUPPORTED_SYNTAX" ]; then
            OUTTEXT+="-unsupported_syntax, "
            C_UNSUPPORTED_SYNTAX=`expr $C_UNSUPPORTED_SYNTAX + 1`
            printf "!Warning! "
            printf "Ultimate says: Unsupported syntax.\n"
            continue;
        fi

        if [ "$RESULT_TIMEOUT" ]; then
            OUTTEXT+="+timeout, "
            C_RESULT_TIMEOUT=`expr $C_RESULT_TIMEOUT + 1`
            printf "!Warning! "
            printf "TraceAbstraction terminated after $RUNTIME and says: Timeout.\n"
            continue;
        fi


        if [ "$RESULT_SAFE" ]; then
            if [ "$PROGRAM_SAFE" ]; then
                OUTTEXT+="+success, "
                C_SUCCESS=`expr $C_SUCCESS + 1`
                printf "Success. "
                printf "TraceAbstraction terminated after $RUNTIME and says: Program is safe. "
                printf "$WHO_DEFINED_SOLUTION Program is safe.\n"
                continue;
            fi
            if [ "$PROGRAM_UNSAFE" ]; then
                OUTTEXT+="-inverted, "
                C_INVERTED=`expr $C_INVERTED + 1`
                printf "!!!FAIL!!! "
                printf "TraceAbstraction terminated after $RUNTIME and says: Program is safe. "
                printf "$WHO_DEFINED_SOLUTION Program is unsafe.\n"
                continue;
            fi
            OUTTEXT+="?safe, "
            C_RESULT_STRANGE=`expr $C_RESULT_STRANGE + 1`
            printf "!Warning! "
            printf "TraceAbstraction terminated after $RUNTIME and says: Program is safe. "
            printf "$WHO_DEFINED_SOLUTION \n"
            continue;
        fi

        if [ "$RESULT_UNSAFE" ]; then
            if [ "$PROGRAM_UNSAFE" ]; then
                OUTTEXT+="+success, "
                C_SUCCESS=`expr $C_SUCCESS + 1`
                printf "Success. "
                printf "TraceAbstraction terminated after $RUNTIME and says: Program is unsafe. "
                printf "$WHO_DEFINED_SOLUTION Program is unsafe.\n"
                continue;
            fi
            if [ "$PROGRAM_SAFE" ]; then
                OUTTEXT+="-inverted, "
                C_INVERTED=`expr $C_INVERTED + 1`
                printf "!!!FAIL!!! "
                printf "TraceAbstraction terminated after $RUNTIME and says: Program is unsafe. "
                printf "$WHO_DEFINED_SOLUTION Program is safe.\n"
                continue;
            fi
            OUTTEXT+="?unsafe, "
            C_RESULT_STRANGE=`expr $C_RESULT_STRANGE + 1`
            printf "!Warning! "
            printf "TraceAbstraction terminated after $RUNTIME and says: Program is unsafe. "
            printf "$WHO_DEFINED_SOLUTION \n"
            continue;
        fi

        if [ "$RESULT_UNKNOWN" ]; then
            OUTTEXT+="+unknown, "
            C_RESULT_UNKNOWN=`expr $C_RESULT_UNKNOWN + 1`
            if [ "$PROGRAM_UNSAFE" ]; then
                printf "!Warning!"
                printf "TraceAbstraction terminated after $RUNTIME and says: Can not determine feasibility of counterexample."
                printf "$WHO_DEFINED_SOLUTION Program is unsafe.\n"
                continue;
            fi
            if [ "$PROGRAM_SAFE" ]; then
                printf "!Warning! "
                printf "TraceAbstraction terminated after $RUNTIME and says: Can not determine feasibility of counterexample."
                printf "$WHO_DEFINED_SOLUTION Program is safe.\n"
                continue;
            fi
            printf "!Warning! "
            printf "TraceAbstraction terminated after $RUNTIME and says: Can not determine feasibility of counterexample."
            printf "$WHO_DEFINED_SOLUTION \n"
            continue;
        fi

        if [ "$RESULT_NORESULT" ]; then
            OUTTEXT+="+no_result, "
            C_RESULT_NORESULT=`expr $C_RESULT_NORESULT + 1`
            printf "!Warning! "
            printf "Ultimate Automizer terminated after $RUNTIME and says: No Result."
            
            
            if [ "$RESULT_PROVEN_TERMINATION" ]; then
                        printf "Termination proven"
            fi
            
            if [ "$RESULT_NOTPROVEN_TERMINATION" ]; then
                        printf "Unable to prove termination"
            fi
            continue;
        fi





        if [ "$INITIALIZED" ]; then
            OUTTEXT+="-initialized, "
            C_INITIALIZED=`expr $C_INITIALIZED + 1`
            printf "!!!FAIL!!! started Ultimate, received no answer after $timeout seconds"
        else
            OUTTEXT+="-unkown_error, "
            C_UNKNOWN_ERROR=`expr $C_UNKNOWN_ERROR + 1`
            printf "!!!FAIL!!! unknown program behaviour"
        fi

    done;
    
    # FILE: new line
    OUTTEXT+="
"
    
    echo "";
done;

# FILE: write to file
echo "-- writing analysis --"
echo "$OUTTEXT" > "../../benchmark.csv"

# FILE: write statistics
echo "-- writing statistics --"
/bin/cat << EOM > "../../statistics.csv"
C_EXCEPT, $C_EXCEPT
C_Z3CRASH1, $C_Z3CRASH1
C_KILLED, $C_KILLED
C_Z3CRASH1, $C_Z3CRASH1
C_Z3CRASH2, $C_Z3CRASH2
C_Z3ERROR7, $C_Z3ERROR7
C_Z3ERROR, $C_Z3ERROR
C_Z3Z3NativeCodeException, $C_Z3Z3NativeCodeException
C_BUG_22, $C_BUG_22
C_BUG_24, $C_BUG_24
C_EXCEPTION, $C_EXCEPTION
C_OOM_HEAP, $C_OOM_HEAP
C_OOM_GC, $C_OOM_GC
C_ASSERTION_ERROR, $C_ASSERTION_ERROR
C_JVMCRASH, $C_JVMCRASH
C_RESULT_SYNTAX_GOOD, $C_RESULT_SYNTAX_GOOD
C_RESULT_SYNTAX_BAD, $C_RESULT_SYNTAX_BAD
C_RESULT_SYNTAX_UNKNOWN, $C_RESULT_SYNTAX_UNKNOWN
C_UNSUPPORTED_SYNTAX, $C_UNSUPPORTED_SYNTAX
C_RESULT_TIMEOUT, $C_RESULT_TIMEOUT
C_RESULT_SUCCESS, $C_RESULT_SUCCESS
C_RESULT_INVERTED, $C_RESULT_INVERTED
C_RESULT_STRANGE, $C_RESULT_STRANGE
C_RESULT_UNKNOWN, $C_RESULT_UNKNOWN
C_RESULT_NORESULT, $C_RESULT_NORESULT
C_INITIALIZED, $C_INITIALIZED
C_UNKNOWN_ERROR, $C_UNKNOWN_ERROR
EOM

cd -