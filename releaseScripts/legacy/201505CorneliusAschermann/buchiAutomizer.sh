#!/bin/sh
if [ ! "$1" ]; then
    echo "First argument has to be the program that we analyze"
    exit
fi
Ultimate_OUTPUT=`./Ultimate --console ./AutomizerAndBuchiAutomizerCWithBlockEncoding.xml "$1" --settings ./BuchiAutomizer.epf`

RESULT_MEMSAFE=`echo "$Ultimate_OUTPUT" | grep "AllSpecificationsHoldResult: All specifications hold"`
RESULT_NOTMEMSAFE=`echo "$Ultimate_OUTPUT" | grep "CounterExampleResult"`
RESULT_PROVEN_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Buchi Automizer proved that your program is terminating"`
RESULT_UNKNOWN_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Buchi Automizer is unable to decide termination"`
RESULT_FALSE_TERMINATION=`echo "$Ultimate_OUTPUT" | grep "Nonterminating execution"`


if [ "$RESULT_MEMSAFE" ]; then
	echo "MEMORYSAFE"
fi

if [ "$RESULT_NOTMEMSAFE" ]; then
	echo "NOT_MEMORYSAFE"
fi

if [ "$RESULT_PROVEN_TERMINATION" ]; then
	echo "TERMINATING"
fi
    
if [ "$RESULT_FALSE_TERMINATION" ]; then
	echo "NONTERMINATING"
fi
    
if [ "$RESULT_UNKNOWN_TERMINATION" ]; then
	echo "UNKNOWN"
fi

#echo ""
echo "$Ultimate_OUTPUT" >&2
