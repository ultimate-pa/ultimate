#!/bin/bash
Ultimate_PATH=`pwd`;
Machine=`uname -m`;
if [ $Machine="i686" ]; then
  Machine=x86;
fi
UltimateEXE="trunk/source/BA_SiteRepository/target/products/UltimateProductCommandLine/linux/gtk/$Machine/Ultimate";
echo $UltimateEXE
TimeLimit=60;

#cd "$1"
#files=`ls *.fat`;
files=`find "$1" -name "*.ats"|sort`
#settings=`ls $Ultimate_PATH/trunk/examples/settings`



for f in $files;
do

echo "$Ultimate_PATH/$UltimateEXE --console $Ultimate_PATH/trunk/examples/toolchains/AutomataScriptInterpreter.xml $f"
printf "Testing " 
printf $f
printf "    "
printf "*** "

Ultimate_OUTPUT=`bash -c "ulimit -t $TimeLimit; $Ultimate_PATH/$UltimateEXE --console $Ultimate_PATH/trunk/examples/toolchains/AutomataScriptInterpreter.xml "$f" 2>&1"`

ERROR_OCCURRED=`echo "$Ultimate_OUTPUT" | grep "ERROR"`
#EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "has thrown an Exception!"`
EXCEPTION=`echo "$Ultimate_OUTPUT" | grep "Exception"`
RESULT_CORRECT=`echo "$Ultimate_OUTPUT" | grep "All testcases passed"`
RESULT_INCORRECT=`echo "$Ultimate_OUTPUT" | grep "Some testcases failed"`
RUNTIME=`echo "$Ultimate_OUTPUT" | grep "AutomataScriptInterpreter took" | cut -c82-`

if [ "$RESULT_CORRECT" ]; then
   printf "successful termination after "
   printf "$RUNTIME"
   printf " ***** "
   printf "result correct"
fi

if [ "$RESULT_INCORRECT" ]; then
   printf "successful termination after "
   printf "$RUNTIME"
   printf " !!!!! "
   printf "result incorrect !!!!!"
fi

if [ "$ERROR_OCCURRED" ]; then
   printf "!!!!! ERROR !!!!!"
fi

if [ "$EXCEPTION" ]; then
   printf "!!!!! EXCEPTION THROWN !!!!!"
fi

printf "\n"


done;
#cd -
