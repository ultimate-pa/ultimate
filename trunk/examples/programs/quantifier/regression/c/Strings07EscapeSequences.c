//#Safe
/* 
 * Check if handle escape sequence in char literals and string 
 * literals as defined in C11 6.4.4.4.
 * 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-03-04
 * 
 */

#include <stdio.h>

int main(void) {
    // Escape sequences that are defined in 6.4.4.4.3
    // the exact numerical values are implementation defined
    // In Ultimate we use the values that we observed on an
    // x86 Linux machine
    char myCharArray[5] = "\xFF\31\am";
    if (myCharArray[0] != -1) {
        printf("error");
        //@ assert \false;
    }
    if (myCharArray[1] != 25) {
        printf("error");
        //@ assert \false;
    }
    if (myCharArray[2] != 7) {
        printf("error");
        //@ assert \false;
    }
    if (myCharArray[3] != 109) {
        printf("error");
        //@ assert \false;
    }
    if (myCharArray[4] != 0) {
        printf("error");
        //@ assert \false;
    }
    return 0;
}

