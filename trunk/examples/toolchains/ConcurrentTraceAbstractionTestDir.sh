#!/bin/bash
Ultimate_PATH=`pwd`;
UltimateEXE="trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86/Ultimate"
TimeLimit=1000;

cd "$1"
#for f in `ls *.bpl`;
files=`find . -name "*.bpl" -o -name "*.c"|sort`
settings=`ls $Ultimate_PATH/trunk/examples/settings/TraceAbstractionConcurrent`

for f in $files;
do

KEYWORD_SYNTAX=`head -n 1 "$f" | grep "#Syntax"`
KEYWORD_CSAFE=`head -n 1 "$f" | grep "#cSafe"`
KEYWORD_CUNSAFE=`head -n 1 "$f" | grep "#cUnsafe"`
VCCPRELUDE=`head -n 1 "$f" | grep "#VccPrelude"`

PROGRAM_SAFE=
PROGRAM_UNSAFE=

if [ "$KEYWORD_CSAFE" ]; then 
    PROGRAM_SAFE="1"
    PROGRAM_UNSAFE=
fi

if [ "$KEYWORD_CUNSAFE" ]; then 
    PROGRAM_SAFE=
    PROGRAM_UNSAFE="1"
fi

EXTENSION=${f##*.}
TOOLCHAIN="unset"
if [ "$EXTENSION" == "bpl" ]; then
    TOOLCHAIN="$Ultimate_PATH/trunk/examples/toolchains/TraceAbstractionConcurrent.xml"
fi

if [ "$EXTENSION" == "c" ]; then
    TOOLCHAIN="$Ultimate_PATH/trunk/examples/toolchains/TraceAbstractionC.xml"
fi


for s in $settings
do

#Ultimate_OUTPUT=`$Ultimate_PATH/console/eclipse/Ultimate --console $Ultimate_PATH/examples/toolchains/TraceAbstraction.xml $f --prelude $Ultimate_PATH/examples/VCC/VccPrelude.bpl --settings $Ultimate_PATH/examples/toolchains/TraceAbstractionLowTheoremProverUsage.settings 2>&1`

if [ "$VCCPRELUDE" ]; then 
    Ultimate_OUTPUT=`bash -c "ulimit -t $TimeLimit; $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$f" --prelude "$Ultimate_PATH/trunk/examples/programs/translated-vcc/Vcc2Prelude.bpl" --settings "$Ultimate_PATH/trunk/examples/settings/TraceAbstractionConcurrent/$s" 2>&1"`    
else
    Ultimate_OUTPUT=`bash -c "ulimit -t $TimeLimit; $Ultimate_PATH/$UltimateEXE --console "$TOOLCHAIN" "$f" --settings "$Ultimate_PATH/trunk/examples/settings/TraceAbstractionConcurrent/$s" 2>&1"`
fi

USED_SETTINGS=`echo "$Ultimate_OUTPUT" | grep "Settings: "`
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
printf "  Settings File: "
printf "$s"
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
    echo "!Warning! AssertionError - Probably Bug #24";
    continue;
fi


if [ "$EXCEPTION"  ]; then
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
RUNTIME=`echo "$Ultimate_OUTPUT" | grep "TraceAbstractionConcurrent took" | cut -c83-`

if [ "$RESULT_SYNTAX" ]; then
    if [ "$KEYWORD_SYNTAX" ]; then
        printf "Success."
        printf "Ultimate says: Syntax error. "
        printf "User annotation says: Syntax error.\n"
        continue;
    fi
    if [ "$PROGRAM_UNSAFE" -o "$PROGRAM_SAFE" -o "$VCCPRELUDE" ]; then
        printf "!!!FAIL!!! "
        printf "Ultimate says: Syntax error. "
        printf "User annotation does not mention any syntax errors \n"
        continue;
    fi
    printf "!Warning! "
    printf "Ultimate says: Syntax error. "
    printf "No user annotation given.\n"
    continue;
fi


if [ "$UNSUPPORTED_SYNTAX" ]; then
    printf "!Warning! "
    printf "Ultimate says: Unsupported syntax.\n"
    continue;
fi

if [ "$RESULT_TIMEOUT" ]; then
    printf "!Warning! "
    printf "TraceAbstraction terminated after $RUNTIME and says: Timeout.\n"
    continue;
fi


if [ "$RESULT_SAFE" ]; then
    if [ "$PROGRAM_SAFE" ]; then
        printf "Success. "
        printf "TraceAbstraction terminated after $RUNTIME and says: Program is safe. "
        printf "User annotation says: Program is safe.\n"
        continue;
    fi
    if [ "$PROGRAM_UNSAFE" ]; then
        printf "!!!FAIL!!! "
        printf "TraceAbstraction terminated after $RUNTIME and says: Program is safe. "
        printf "User annotation says: Program is unsafe.\n"
        continue;
    fi
    printf "!Warning! "
    printf "TraceAbstraction terminated after $RUNTIME and says: Program is safe. "
    printf "No user annotation given.\n"
    continue;
fi

if [ "$RESULT_UNSAFE" ]; then
    if [ "$PROGRAM_UNSAFE" ]; then
        printf "Success. "
        printf "TraceAbstraction terminated after $RUNTIME and says: Program is unsafe. "
        printf "User annotation says: Program is unsafe.\n"
        continue;
    fi
    if [ "$PROGRAM_SAFE" ]; then
        printf "!!!FAIL!!! "
        printf "TraceAbstraction terminated after $RUNTIME and says: Program is unsafe. "
        printf "User annotation says: Program is safe.\n"
        continue;
    fi
    printf "!Warning! "
    printf "TraceAbstraction terminated after $RUNTIME and says: Program is unsafe. "
    printf "No user annotation given.\n"
    continue;
fi

if [ "$RESULT_UNKNOWN" ]; then
    if [ "$PROGRAM_UNSAFE" ]; then
        printf "!Warning!"
        printf "TraceAbstraction terminated after $RUNTIME and says: Can not determine feasibility of counterexample."
        printf "User annotation says: Program is unsafe.\n"
        continue;
    fi
    if [ "$PROGRAM_SAFE" ]; then
        printf "!Warning! "
        printf "TraceAbstraction terminated after $RUNTIME and says: Can not determine feasibility of counterexample."
        printf "User annotation says: Program is safe.\n"
        continue;
    fi
    printf "!Warning! "
    printf "TraceAbstraction terminated after $RUNTIME and says: Can not determine feasibility of counterexample."
    printf "No user annotation given.\n"
    continue;
fi

if [ "$RESULT_UNKNOWN" ]; then
    printf "!Warning! "
    printf "TraceAbstraction terminated after $RUNTIME and says: Insufficient iterations."
    continue;
fi



if [ "$INITIALIZED" ]; then
      echo "!!!FAIL!!! started Ultimate, received no answer after $TimeLimit seconds"
    else
      echo "!!!FAIL!!! unknown program behaviour"
fi

done;
echo "";
done;
cd -
