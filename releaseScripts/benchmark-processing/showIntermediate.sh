#!/bin/bash
FILE=${1}
for j in `grep -oh 'Toolchain:[^ ]*\.xml' ${FILE} | sort | uniq`
do
    TOOLCHAIN=${j#Toolchain:}
        echo $TOOLCHAIN
        echo "--"
        RTR=""
        for i in `grep -oh 'Settings:[^ ]*' ${FILE} | sort | uniq`
        do
                SETTING=${i#Settings:}
                SUCCESS=`ack "with SUCCESS" "$FILE" | grep "$SETTING.*$TOOLCHAIN" | wc -l`
                FAILURE=`ack "with FAIL" "$FILE" | grep "$SETTING.*$TOOLCHAIN" | wc -l`
                UNKNOWN=`ack "with UNKNOWN" "$FILE" | grep "$SETTING.*$TOOLCHAIN" | wc -l`
                TOTAL=$((SUCCESS+FAILURE+UNKNOWN))
                if [ $TOTAL -gt "0" ]; then
                        RTR="${RTR}S: $SUCCESS F: $FAILURE U: $UNKNOWN T: $TOTAL $SETTING\n"
                fi
        done
        echo -e "$RTR" | column -t
        echo "--"
done

