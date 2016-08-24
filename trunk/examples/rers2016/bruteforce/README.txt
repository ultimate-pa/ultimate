First, configure the inpute sequences to try by setting the constants

INPUT_LENGTH    The maximum length of the input sequences
INPUT_MIN       The smalles value of the input
INPUT_MAX       The largest value of the input

To compile (For example Problem17):

        gcc -o Problem17 Problem17.c

** This will take a minute or two (more like 5)

To run:

First, execute the program:

        ./Problem17 2> output17.txt 1> /dev/null
        
** How long this needs depends on your configuration above, a length of 5 is 
   fairly quick

Then, process the output:

        awk -e '{print $1}' output17.txt | sort | uniq

You will obtain a list of the labels reached.
