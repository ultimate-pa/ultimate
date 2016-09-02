First, configure the input sequences to try by setting the constants

INPUT_LENGTH    The maximum length of the input sequences
INPUT_MIN       The smallest value of the input
INPUT_MAX       The largest value of the input

To compile (For example Problem17):

        gcc -o Problem17 Problem17.c

** This will take a minute or two (more like 5)
NOTE: clang is a lot faster

To run:

First, execute the program:

        ./Problem17 INPUT_LENGTH > output17.txt
        
** How long this needs depends on your configuration above, a length of 10 is 
   fairly quick

Then, process the output:

        awk -e '{print $1}' output17.txt | sort -Vu

You will obtain a list of the labels reached.
