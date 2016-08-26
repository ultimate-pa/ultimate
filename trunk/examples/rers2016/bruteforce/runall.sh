#!/bin/sh

for i in `seq 10 18`; 
do
        echo -n "Compiling Problem$i..."
        gcc -o Problem$i Problem$i.c && echo "ok." && echo -n "Running Problem$i..." && ./Problem$i 2> output$i.txt 1> /dev/null 
        echo "done."
        echo -n "Processing output for Problem$i..."
        awk '{print $1}' output$i.txt | sort | uniq > result$i.txt
        echo "done."
done