#!/bin/bash
Ultimate_PATH=`pwd`;

Timeout=80;


examplesFolder=$1;
if [ ! -e "$examplesFolder" ]; then
    echo "Folder $examplesFolder does not exist"
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

#------------------------------------------------------------------------------
# set enable assertions
#------------------------------------------------------------------------------
UltimateINI="trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/$arch/Ultimate.ini";
if [ ! -e "$UltimateINI" ]; then
    echo "unable to find Ultimate.ini $UltimateINI"
    exit
fi

# detect if -da is already set
DA=`grep "\-da$" "$UltimateINI"`
if [ "$DA" ]; then
	echo "assertions disabled - while writing this script this was not expected"
	exit
fi

# add -ea if not already added
EA=`grep "\-ea" "$UltimateINI"`
if [ ! "$EA" ]; then
	echo "-ea" >> "$UltimateINI"
	echo "adding -ea to $UltimateINI"
fi

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
RUNTIME=`echo "$Ultimate_OUTPUT" | grep "AutomataScriptInterpreter took" | cut -c82-`


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

