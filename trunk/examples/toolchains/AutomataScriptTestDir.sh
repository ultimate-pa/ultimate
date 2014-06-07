#!/bin/bash
Ultimate_PATH=`pwd`;

assertionString=$1

if [[ "$assertionString" != "-da" && "$assertionString" != "-ea" ]]; then
	echo "first argument has to be -ea or -da"
	exit
fi

shift


Timeout=80;


examplesFolder=$1;
if [ ! -e "$examplesFolder" ]; then
    echo "Folder $examplesFolder does not exist"
    exit
fi



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
UltimateEXE="trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/$arch/Ultimate";
if [ ! -e "$UltimateEXE" ]; then
    echo "unable to find Ultimate executable $UltimateEXE"
    exit
fi

function setAssertions {
    #------------------------------------------------------------------------------
    # set enable assertions
    #------------------------------------------------------------------------------
    UltimateINI="trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/$arch/Ultimate.ini";
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

files=`find "$examplesFolder" -name "*.ats"|sort`

for f in $files;
do


#echo ""
#echo  "$Ultimate_PATH/$UltimateEXE --console $Ultimate_PATH/trunk/examples/toolchains/AutomataScriptInterpreter.xml $f"

printf "Testing " 
printf $f
printf "    "
printf "*** "

Ultimate_OUTPUT=`bash -c "ulimit -t $Timeout; $Ultimate_PATH/$UltimateEXE --console $Ultimate_PATH/trunk/examples/toolchains/AutomataScriptInterpreter.xml "$f" 2>&1"`

ERROR_OCCURRED=`echo "$Ultimate_OUTPUT" | grep "ERROR"`
#EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "has thrown an Exception!"`
EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "Exception"`
RESULT_CORRECT=`echo "$Ultimate_OUTPUT" | grep "All assert statements have been evaluated to true"`
RESULT_INCORRECT=`echo "$Ultimate_OUTPUT" | grep "Some assert statements have been evaluated to false"`
RESULT_NOTESTCASES=`echo "$Ultimate_OUTPUT" | grep "not used any assert statement in your automata"`
RESULT_TIMEOUT=`echo "$Ultimate_OUTPUT" | grep "Timeout during interpretation of automata script"`
RESULT_OOM=`echo "$Ultimate_OUTPUT" | grep "Run out of memory during interpretation of automata script"`
RUNTIME=`echo "$Ultimate_OUTPUT" | grep "AutomataScriptInterpreter took" | cut -c83-94`


if [ "$RESULT_TIMEOUT" ]; then
   printf "timeout after "
   printf "$RUNTIME"
   printf " ____________ "
   printf "\n"
fi

if [ "$RESULT_OOM" ]; then
   printf "out of memory after "
   printf "$RUNTIME"
   printf " ____________ "
   printf "\n"
fi

if [ "$RESULT_CORRECT" ]; then
   printf "successful termination after "
   printf "$RUNTIME"
   printf " ******* "
   printf "result correct"
   printf "\n"
fi

if [ "$RESULT_INCORRECT" ]; then
   printf "successful termination after "
   printf "$RUNTIME"
   printf " !!!!! "
   printf "result incorrect !!!!!"
   printf "\n"
fi

if [ "$ERROR_OCCURRED" ]; then
   printf "!!!!! ERROR !!!!!"
   printf "\n"
   echo "$ERROR_OCCURRED"
fi

if [ "$EXCEPTION" ]; then
   printf "!!!!! EXCEPTION THROWN !!!!!"
   printf "\n"
   echo "$EXCEPTION"
fi

if [ "$RESULT_NOTESTCASES" ]; then
   printf "successful termination after "
   printf "$RUNTIME"
   printf " ****** "
   printf "No testcases defined!"
   printf "\n"
fi




done;

