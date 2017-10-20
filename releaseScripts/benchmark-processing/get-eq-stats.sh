#!/bin/bash 
# small script to find files that contain certain statistics using the csvfix tool 


count=0
valid=0

declare -A statistics=( 
["MAX_WEQGRAPH_SIZE"]=0
["MAX_SIZEOF_WEQEDGELABEL"]=0
["NO_SUPPORTING_EQUALITIES"]=0
["NO_SUPPORTING_DISEQUALITIES"]=0
)

declare -A exceptions
declare -A timeouts

known_exceptions=( 
"UnsupportedSyntaxResult"
"TypeErrorResult"
"SyntaxErrorResult"
)

known_timeouts=(
"Cannot interrupt operation gracefully because timeout expired. Forcing shutdown"
"Toolchain execution was canceled (user or tool) before executing"
)

find "$1" -type f -iname '*.log' | (while read line; do 
    count=$((count+1))
    
    stats=`grep -A6 'StatisticsResult: ArrayEqualityDomain' "$line"`
    if [ $? -ne 0 ]; then 
        if grep -q 'ExceptionOrErrorResult' $line; then
            exc=`grep -A1 'ExceptionOrErrorResult' $line | grep -v 'ExceptionOrErrorResult'`
            exceptions["$exc"]=$((exceptions["$exc"]+1))
            continue 
        fi
		for i in "${known_exceptions[@]}"; do 
			if grep -q "$i" $line; then
				exceptions["$i"]=$((exceptions["$i"]+1))
				continue 2
			fi		
		done

        if grep -qP 'Timeout.*Result' $line; then
            exc=`grep -A1 -P 'Timeout.*Result' $line | grep -vP 'Timeout.*Result'`
            timeouts["$exc"]=$((timeouts["$exc"]+1))
            continue 
        fi
		for i in "${known_timeouts[@]}"; do 
			if grep -q "$i" $line; then
				timeouts["$i"]=$((timeouts["$i"]+1))
				continue 2
			fi		
		done
       
        echo "$line contains unhandled result"
        continue
    fi

    valid=$((valid+1))

    for i in "${!statistics[@]}"; do 
        val=`echo $stats | grep -oP "$i\s*:\s*[0-9]+" | cut -d ':' -f 2`
        statistics[$i]=$((statistics[$i]+val))
    done
done

echo "$valid of $count valid"
echo "Sum" 
for i in "${!statistics[@]}"; do 
    echo "$i=${statistics[$i]}"
done

tot=0
for i in ${exceptions[@]}; do
  let tot+=$i
done

echo ""
echo "Exceptions ($tot)"
for ex in "${!exceptions[@]}"; do 
    echo "${exceptions[$ex]} : $ex"; 
done

tot=0
for i in ${timeouts[@]}; do
  let tot+=$i
done

echo ""
echo "Timeouts ($tot)"
for ex in "${!timeouts[@]}"; do 
    echo "${timeouts[$ex]} : $ex"; 
done
)



