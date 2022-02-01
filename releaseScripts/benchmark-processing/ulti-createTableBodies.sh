#!/bin/bash

if [ ! -f "$1" ]
then
	echo "Cannot read input file"
	exit -1;
fi
INPUT=${1}

echo "Processing "${INPUT}"..."

LOGFILE="result"
#FOLDERS=( locks recursive ntdrivers-simplified ssh-simplified systemc heap-manipulation list-properties ldv-regression loops )
FOLDERS=( systemc )
TOOLS=( AutomizerC.xml )
#SETTINGS=( Princess_Interpolation.epf SMTInterpol_Interpolation.epf SMTInterpol_SP-IC-LV.epf Z3_SP-IC-LV.epf SMTInterpol_SP-IC.epf Z3_SP-IC.epf Z3_SP-LV.epf Z3_SP.epf )
SETTINGS=( Princess_Interpolation-mem.epf SMTInterpol_Interpolation-mem.epf SMTInterpol_SP-IC-LV-mem.epf Z3_SP-IC-LV-mem.epf SMTInterpol_SP-IC-mem.epf Z3_SP-IC-mem.epf Z3_SP-LV-mem.epf Z3_SP-mem.epf )

rm $LOGFILE

TMPPATH=/tmp

cp "${INPUT}" "${TMPPATH}/input"
INPUT=$TMPPATH/input
REALLOG=$LOGFILE
LOGFILE=$TMPPATH/$LOGFILE

for folder in "${FOLDERS[@]}"
do
	for tool in "${TOOLS[@]}"
	do
		FIRST=true
		for setting in "${SETTINGS[@]}"
		do
			if $FIRST ; 
			then 
				ALL=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "Finishing" | wc -l`
				PRE="\multirow{8}{*}{\folder{"$folder"}} & \multirow{8}{*}{"$ALL"}"
				FIRST=false
			else 
				PRE=" &"
			fi
			SUCCESS=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "SUCCESS" | wc -l`
			TIMEOUT=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "TIMEOUT" | wc -l`
			OOM=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "OutOf" | wc -l`
			QF=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "Cannot create quantifier in quantifier-free logic" | wc -l`
			NAS=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "Cannot interpolate" | wc -l`			
			FAIL=`grep "${folder}" "$INPUT" | grep "${tool}" | grep "${setting}" | grep "Finishing" | grep -v "SUCCESS" | grep -v "TIMEOUT" | grep -v "OutOf" | grep -v "Cannot create quantifier in quantifier-free logic" | grep -v "Cannot interpolate" | wc -l`
			echo $PRE" & "$setting" & "$SUCCESS" & "$TIMEOUT" & "$OOM" & "$QF" & "$NAS" & "$FAIL" \\\\" >> ${LOGFILE}
		done
		echo "\\midrule" >> ${LOGFILE}
	done
done

rm "$INPUT"

sed -i 's/Princess_Interpolation.*.epf/\\princessip/g' ${LOGFILE}
sed -i 's/SMTInterpol_Interpolation.*.epf/\\smtinterpolip/g' ${LOGFILE}
sed -i 's/SMTInterpol_SP-IC-LV.*.epf/\\sispiclv/g' ${LOGFILE}
sed -i 's/Z3_SP-IC-LV.*.epf/\\zzzspiclv/g' ${LOGFILE}
sed -i 's/SMTInterpol_SP-IC.*.epf/\\sispic/g' ${LOGFILE}
sed -i 's/Z3_SP-IC.*.epf/\\zzzspic/g' ${LOGFILE}
sed -i 's/Z3_SP-LV.*.epf/\\zzzsplv/g' ${LOGFILE}
sed -i 's/Z3_SP.*.epf/\\zzzsp/g' ${LOGFILE}

mv $LOGFILE $REALLOG
