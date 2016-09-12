#!/bin/bash
FILE=${1}
for i in `grep -oh 'Settings:[^ ]*' target/surefire-reports/de.uni_freiburg.informatik.ultimatetest.suites.svcomp.SVCOMP16TestSuite/IncrementalLogWithVMParameters\ 2016-04-12_13-41-39-470-incremental.log | sort | uniq`
do
	SETTING=${i#Settings:}
	SUCCESS=`ack SUCCESS "$FILE" | grep "$SETTING" | wc -l`
	echo "$SUCCESS $SETTING"
done


